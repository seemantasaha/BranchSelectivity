package ucsb.vlab.branchselectivity;

import com.martiansoftware.util.StringUtils;
import spoon.reflect.cu.SourcePosition;
import spoon.reflect.path.CtPath;
import spoon.reflect.path.CtRole;
import spoon.reflect.visitor.CtVisitor;
import spoon.reflect.visitor.chain.CtConsumableFunction;
import spoon.reflect.visitor.chain.CtFunction;
import spoon.reflect.visitor.chain.CtQuery;
import spoon.support.reflect.declaration.CtInterfaceImpl;
import vlab.cs.ucsb.edu.ModelCounter;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.lang.annotation.Annotation;
import java.util.*;
import java.lang.String;
import java.math.BigDecimal;

import javafx.util.Pair;

import org.apache.commons.io.FileUtils;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.BufferedWriter;
import java.io.FileWriter;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import spoon.*;
import spoon.compiler.ModelBuildingException;
import spoon.reflect.code.*;
import spoon.reflect.declaration.*;
import spoon.reflect.factory.Factory;
import spoon.reflect.factory.CoreFactory;
import spoon.reflect.factory.FactoryImpl;
import spoon.reflect.reference.CtArrayTypeReference;
import spoon.reflect.reference.CtExecutableReference;
import spoon.reflect.reference.CtTypeReference;
import spoon.reflect.visitor.Filter;
import spoon.support.DefaultCoreFactory;
import spoon.support.compiler.jdt.JDTBasedSpoonCompiler;
import spoon.support.reflect.code.*;
import spoon.support.reflect.reference.CtArrayTypeReferenceImpl;
import spoon.reflect.declaration.CtType;
import spoon.compiler.Environment;
import spoon.support.StandardEnvironment;
import spoon.reflect.CtModel;
import spoon.reflect.visitor.filter.TypeFilter;

import javax.print.DocFlavor;

public class BranchSelectivity {

    private static Map<Pair<String,String>, Integer> selectiveBranchMap = new HashMap<Pair<String,String>, Integer>();
    private static Set<Pair<String,String>> variableInConstraint = new HashSet<Pair<String,String>>();
    private static int index = 0;
    private static String sourceDirectory;
    public static BufferedWriter bw;
    public static boolean MethodInCondition;
    public static boolean MultiTrackIssueFlag;
    public static boolean CharAtFlag;
    public static boolean CharAtLGEQFlag;
    public static boolean EqualFlag;
    public static Map<String, Integer> varIndexMap;
    public static Map<String, ArrayList<String>> lineConsMap = new HashMap<String, ArrayList<String>>();
    public static ArrayList<String> methodList = new ArrayList<>();
    public static BufferedWriter bwFeature;
    public static Map<String, String> methodFeatureMap = new HashMap<>();
    public static Map<String, Boolean> methodFeatureFlagMap = new HashMap<>();

    private boolean assertionEmpty;

    private int numberOfClasses = 0;
    private int numberOfMethods = 0;
    private int numberOfBranchesWithLoop = 0;
    private int numberOfBranches = 0;
    private int numberOfBranchesWithmethodInvocation = 0;
    private int numberOfBranchesWithUnaryOp = 0;
    private int numberOfBranchesWithBinOp = 0;
    private int numberOfBranchesConsidered = 0;
    private int numberOfSelectiveBranches = 0;

    private long processingTime;

    private void readIntervalAnalysisResults() {
        BufferedReader objReader = null;
        try {
            String strCurrentLine;

            objReader = new BufferedReader(new FileReader(sourceDirectory + "/branch_interval_results.txt"));

            while ((strCurrentLine = objReader.readLine()) != null) {

                //String className = strCurrentLine.split(".java")[0];
                //String lineNumber = strCurrentLine.split(":")[1].split("\t")[0];
                String info[] = strCurrentLine.split("\t");
                String classLine = info[0];
                if (lineConsMap.containsKey(classLine)) {
//                    String clp[] = classLine.split("_");
//                    if (clp.length == 2) {
//                        int num = Integer.parseInt(clp[1]) + 1;
//                        classLine = classLine + "_" + num;
//                    } else {
//                        classLine = classLine + "_2";
//                    }
                } else {
                    if (info.length == 1) {
                        lineConsMap.put(classLine, null);
                    } else {
                        String cons[] = info[1].split(", ");
                        ArrayList<String> consList = new ArrayList<String>();
                        for (String con : cons) {
                            consList.add(con);
                        }
                        lineConsMap.put(classLine, consList);
                    }
                }
            }

        } catch (IOException e) {

            e.printStackTrace();

        } finally {

            try {
                if (objReader != null)
                    objReader.close();
            } catch (IOException ex) {
                ex.printStackTrace();
            }
        }
    }

    private String reshapeString(String string) {
        string = string.replace(".", "");
        string = string.replace(" ", "");
        string = string.replace("()", "");
        string = string.replace("(", "");
        string = string.replace(")", "");
        string = string.replace("[]", "");
        string = string.replace("[", "");
        string = string.replace("]", "");
        string = string.replace(",", "");
        string = string.replace("+", "");
        string = string.replace("-", "");
        string = string.replace("_", "");

        if(string.equals("trim")) {
            string = "trimVar";
        }

        return string;
    }

    private String handleMethodInvocations(CtElement op) {

        String string = "";

        CtInvocationImpl invocationImpl = (CtInvocationImpl) op;

        //write code to handle all string operations
        //System.out.println(invocationImpl.getExecutable().getDeclaringType());
        if(invocationImpl.getExecutable().getType() != null && (invocationImpl.getExecutable().getType().toString().equals("int")
                || invocationImpl.getExecutable().getType().toString().equals("java.lang.String"))) {

            if (invocationImpl.getExecutable().getDeclaringType().toString().equals("java.lang.String")
                    && invocationImpl.getExecutable().getSimpleName().equals("length")) {
                String var = invocationImpl.getTarget().toString();
                var = reshapeString(var);
                if(invocationImpl.getTarget() instanceof CtInvocationImpl) {
                    CtInvocationImpl impl = ((CtInvocationImpl) invocationImpl.getTarget());
                    var = impl.getTarget().toString();
                    var += "_" + impl.getExecutable().getSimpleName();
                    var = reshapeString(var);
                }
                variableInConstraint.add(new Pair<String, String>(var, invocationImpl.getExecutable().getDeclaringType().toString()));
                string = "(len " + var +")";
            } else {
                string = op.toString().replaceAll("[^a-zA-Z0-9]", "");
                variableInConstraint.add(new Pair<String, String>(string, invocationImpl.getExecutable().getType().toString()));
            }
        } else if(invocationImpl.getExecutable().getType() != null && (invocationImpl.getExecutable().getType().toString().equals("boolean")
                || invocationImpl.getExecutable().getType().toString().equals("char"))
                && (invocationImpl.getExecutable().getDeclaringType() != null
                && (invocationImpl.getExecutable().getDeclaringType().toString().equals("java.lang.String")
                || invocationImpl.getExecutable().getDeclaringType().toString().equals("java.lang.CharSequence")
                || invocationImpl.getExecutable().getDeclaringType().toString().equals("java.lang.Character")
                || invocationImpl.getExecutable().getDeclaringType().toString().equals("char")))) {

            if(invocationImpl.getTarget().toString().contains("toString()")) {
                assertionEmpty = true;
            }

            else if (invocationImpl.getExecutable().getSimpleName().equals("equals")) {
                EqualFlag = true;
                String param = processOp((CtElement) invocationImpl.getArguments().get(0));

                if (param.equals("")) {
                    string = "";
                }
                else {
                    if (invocationImpl.getTarget() instanceof  CtLiteralImpl) {
                        string = "(= " + invocationImpl.getTarget().toString() + " " + param + ")";
                    }
                    else if (invocationImpl.getTarget() instanceof CtInvocationImpl) {
                        CtInvocationImpl impl = (CtInvocationImpl) invocationImpl.getTarget();
                        String var = impl.getExecutable().getSimpleName() + "Var";
                        string = "(= " + var + " " + param + ")";
                        variableInConstraint.add(new Pair<String, String>(var, invocationImpl.getExecutable().getDeclaringType().toString()));
                    } else if (invocationImpl.getTarget() instanceof  CtBinaryOperatorImpl) {
                        string = processOp((CtBinaryOperatorImpl)invocationImpl.getTarget());
                        string = string.replaceAll(Pattern.quote("+"), "concat");;
                        string = "(= " + string + " " + param + ")";
                        variableInConstraint.add(new Pair<String, String>(string, "java.lang.String"));
                    } else {
                        String var = invocationImpl.getTarget().toString();
                        var = reshapeString(var);
                        string = "(= " + var + " " + param + ")";
                        variableInConstraint.add(new Pair<String, String>(var, invocationImpl.getExecutable().getDeclaringType().toString()));
                    }
                    if (invocationImpl.getExecutable().getDeclaringType().toString().equals("char")) {
                        if (param.length() == 3 && param.contains("'") && !CharAtFlag) {
                            int ascii = (int) (param.charAt(1));
                            param = "" + ascii;
                        }
                    }
                }
            }

            else if (invocationImpl.getExecutable().getSimpleName().equals("isDigit")) {
                String param = processOp((CtElement) invocationImpl.getArguments().get(0));
                variableInConstraint.add(new Pair<String, String>(invocationImpl.getTarget().toString(), invocationImpl.getExecutable().getDeclaringType().toString()));
                if(param.contains("charAt")) {
                    string = "(or (= " + param + " \"0\")" + "(= " + param + " \"1\")" + "(= " + param + " \"2\")"
                            + "(= " + param + " \"3\")" + "(= " + param + " \"4\")" + "(= " + param + " \"5\")"
                            + "(= " + param + " \"6\")" + "(= " + param + " \"7\")" + "(= " + param + " \"8\")"
                            + "(= " + param + " \"9\"))";
                } else {
                    string = "(or (= " + param + " 0)" + "(= " + param + " 1)" + "(= " + param + " 2)"
                            + "(= " + param + " 3)" + "(= " + param + " 4)" + "(= " + param + " 5)"
                            + "(= " + param + " 6)" + "(= " + param + " 7)" + "(= " + param + " 8)"
                            + "(= " + param + " 9))";
               }
            }

            else if (invocationImpl.getExecutable().getSimpleName().equals("isWhitespace")) {
                String param = processOp((CtElement) invocationImpl.getArguments().get(0));
                variableInConstraint.add(new Pair<String, String>(invocationImpl.getTarget().toString(), invocationImpl.getExecutable().getDeclaringType().toString()));
                if(!CharAtLGEQFlag && ((CtElement) invocationImpl.getArguments().get(0)).toString().contains("charAt")) {
                    string = "(= " + param + " \" \")";
                }
                else {
                    string = "(= " + param + " 32)";
                }
            }

            else if (invocationImpl.getExecutable().getSimpleName().equals("contains")) {
                CtElement elem = (CtElement) invocationImpl.getArguments().get(0);
                String param = processOp(elem);

                if(param.equals("")) {
                    if (elem instanceof CtInvocationImpl) {
                        CtInvocationImpl invocation = (CtInvocationImpl) elem;
                        if (invocation.getType() != null) {
                            param = invocation.getTarget().toString();
                            variableInConstraint.add(new Pair<String, String>(param, invocation.getType().toString()));
                        }
                    }else if(elem instanceof CtBinaryOperatorImpl) {
                        CtBinaryOperatorImpl binOp = (CtBinaryOperatorImpl) elem;
                        param = "binOp";
                        if (binOp.getType() != null) {
                            variableInConstraint.add(new Pair<String, String>(param, binOp.getType().toString()));
                        }
                        else if (binOp.getLeftHandOperand().getType()!= null) {
                            variableInConstraint.add(new Pair<String, String>(param, binOp.getLeftHandOperand().getType().toString()));
                        }
                        else if (binOp.getRightHandOperand().getType()!= null) {
                            variableInConstraint.add(new Pair<String, String>(param, binOp.getRightHandOperand().getType().toString()));
                        }
                    }
                }
                string = invocationImpl.getTarget().toString();
                string = reshapeString(string);
                variableInConstraint.add(new Pair<String, String>(string, invocationImpl.getTarget().getType().toString()));
                string = "(contains " + string + " " + param +")";
            }

            else if (invocationImpl.getExecutable().getSimpleName().equals("startsWith")) {
                CtElement paramElem = (CtElement) invocationImpl.getArguments().get(0);
                if (!(paramElem instanceof CtBinaryOperatorImpl)) {
                    String param = processOp(paramElem);
                    if (invocationImpl.getTarget() instanceof CtInvocationImpl) {
                        CtInvocationImpl impl = (CtInvocationImpl) invocationImpl.getTarget();
                        string = "(startsWith " + reshapeString(impl.getExecutable().getSimpleName()) + "Var" + " " + param + ")";
                        variableInConstraint.add(new Pair<String, String>(reshapeString(impl.getExecutable().getSimpleName()) + "Var", invocationImpl.getExecutable().getDeclaringType().toString()));
                    } else {
                        string = "(startsWith " + reshapeString(invocationImpl.getTarget().toString()) + "Var" + " " + param + ")";
                        variableInConstraint.add(new Pair<String, String>(reshapeString(invocationImpl.getTarget().toString()) + "Var", invocationImpl.getExecutable().getDeclaringType().toString()));
                    }
                }
                //variableInConstraint.add(new Pair<String, String>(invocationImpl.getTarget().toString(), invocationImpl.getExecutable().getDeclaringType().toString()));
                //param = param.replace("\"", "\"(\"");
                //string = "(startsWith " + invocationImpl.getTarget().toString() + " \"" + param +"\" )";
                //string = "(startsWith " + invocationImpl.getTarget().toString() + " " + param +")";
            }

            else if (invocationImpl.getExecutable().getSimpleName().equals("endsWith")) {                CharAtFlag = true;
                CtElement paramElem = (CtElement) invocationImpl.getArguments().get(0);
                if (!(paramElem instanceof CtBinaryOperatorImpl)) {
                    String param = processOp(paramElem);
                    param = reshapeString(param);
                    if (invocationImpl.getTarget() instanceof CtInvocationImpl) {
                        CtInvocationImpl impl = (CtInvocationImpl) invocationImpl.getTarget();
                        String var = reshapeString(impl.getExecutable().getSimpleName()) + "Var";
                        string = "(endsWith " + var + " " + param + ")";
                        variableInConstraint.add(new Pair<String, String>(var, invocationImpl.getExecutable().getDeclaringType().toString()));
                    } else {
                        String var = reshapeString(invocationImpl.getTarget().toString()) + "Var";
                        string = "(endsWith " + var + " " + param + ")";
                        variableInConstraint.add(new Pair<String, String>(var, invocationImpl.getExecutable().getDeclaringType().toString()));
                    }
                }
            }

            else if (invocationImpl.getExecutable().getSimpleName().equals("matches")) {
                MethodInCondition = true;
                String param = processOp((CtElement) invocationImpl.getArguments().get(0));
                variableInConstraint.add(new Pair<String, String>(invocationImpl.getTarget().toString(), invocationImpl.getExecutable().getDeclaringType().toString()));
                param = param.replace("\"","/");
                param = param.replace("^","~");
                string = "(str.in.re " + invocationImpl.getTarget().toString() + " " + param +")";
            }

            else if (invocationImpl.getExecutable().getSimpleName().equals("charAt")) {
                CharAtFlag = true;
                CtElement elem = (CtElement) invocationImpl.getArguments().get(0);
                String param = processOp(elem);

                if(param.equals("")) {
                    if (elem instanceof CtInvocationImpl) {
                        CtInvocationImpl invocation = (CtInvocationImpl) elem;
                        if (invocation.getType() != null) {
                            param = invocation.getTarget().toString();
                            variableInConstraint.add(new Pair<String, String>(param, invocation.getType().toString()));
                        }
                    }else if(elem instanceof CtBinaryOperatorImpl) {
                        CtBinaryOperatorImpl binOp = (CtBinaryOperatorImpl) elem;
                        param = "binOp";
                        if (binOp.getType() != null) {
                            variableInConstraint.add(new Pair<String, String>(param, binOp.getType().toString()));
                        }
                        else if (binOp.getLeftHandOperand().getType()!= null) {
                            variableInConstraint.add(new Pair<String, String>(param, binOp.getLeftHandOperand().getType().toString()));
                        }
                        else if (binOp.getRightHandOperand().getType()!= null) {
                            variableInConstraint.add(new Pair<String, String>(param, binOp.getRightHandOperand().getType().toString()));
                        }
                    }
                }


                string = invocationImpl.getTarget().toString();
                string = reshapeString(string);

                if(CharAtLGEQFlag) {
                    string = string + "Var";
                    if(invocationImpl.getExecutable().getDeclaringType().toString().equals("java.lang.CharSequence")) {
                        variableInConstraint.add(new Pair<String, String>(string, "char" ));
                    } else {
                        variableInConstraint.add(new Pair<String, String>(string, "char"));
                    }
                } else {
                    if (invocationImpl.getExecutable().getDeclaringType().toString().equals("java.lang.CharSequence")) {
                        variableInConstraint.add(new Pair<String, String>(string, "java.lang.String"));
                    } else {
                        variableInConstraint.add(new Pair<String, String>(string, invocationImpl.getExecutable().getDeclaringType().toString()));
                    }
                    string = "(charAt " + string + " " + param + ")";
                }


//                    try {
//                        Double.parseDouble(param);
//                    } catch(NumberFormatException e){
//                        System.err.println("Not numeric!!!");
//                        variableInConstraint.add(new Pair<String, String>(param, "int"));
//                    }
            }


        }
        else if (((CtInvocationImpl) op).getExecutable().toString().equals("isEmpty(java.lang.String)")) {
            String param = ((CtInvocationImpl) op).getArguments().get(0).toString();
            param = reshapeString(param);
            variableInConstraint.add(new Pair<String, String>(param, "java.lang.String"));
            string = "(= \"\" " + param + ")";
        }
        else if (((CtInvocationImpl) op).getExecutable().toString().equals("isEqual(java.lang.String,java.lang.String)")) {
            variableInConstraint.add(new Pair<String, String>(((CtInvocationImpl) op).getArguments().get(0).toString(), "java.lang.String"));
            variableInConstraint.add(new Pair<String, String>(((CtInvocationImpl) op).getArguments().get(1).toString(), "java.lang.String"));
            string = "(= " + ((CtInvocationImpl) op).getArguments().get(0).toString() + " " + ((CtInvocationImpl) op).getArguments().get(1).toString() + ")";
        }
        else if (((CtInvocationImpl) op).getExecutable().toString().equals("min()")) {
            variableInConstraint.add(new Pair<String, String>("min", "int"));
            string = "min";
        }
        else if (((CtInvocationImpl) op).getExecutable().toString().equals("max()")) {
            variableInConstraint.add(new Pair<String, String>("max", "int"));
            string = "max";
        }
        else if (((CtInvocationImpl) op).getExecutable().toString().equals("size()")) {
            variableInConstraint.add(new Pair<String, String>("size", "int"));
            string = "size";
        }
        else {
            assertionEmpty = true;
            //System.out.println("culprit 2");
        }
        return string;
    }

    private String processOp(CtElement op) {
        String string = "";

        if(op instanceof CtBinaryOperatorImpl) {
            //System.out.println("Processing CtBinaryOperatorImpl");
            assertionEmpty = false;
            CtBinaryOperatorImpl binOp = ((CtBinaryOperatorImpl) op);
            string = generateAssertion(binOp.getLeftHandOperand(),binOp.getRightHandOperand(),binOp.getKind());
            //System.out.println("BInary operator string: " + string);
        } else if (op instanceof CtUnaryOperatorImpl) {
            if (((CtUnaryOperatorImpl) op).getOperand() instanceof CtBinaryOperatorImpl) {
                CtBinaryOperatorImpl binOp = ((CtBinaryOperatorImpl) ((CtUnaryOperatorImpl) op).getOperand());
                string = generateAssertion(binOp.getLeftHandOperand(), binOp.getRightHandOperand(), binOp.getKind());
                if(!string.equals(""))
                    string = "(not" + string + ")";
            } else if (((CtUnaryOperatorImpl) op).getOperand() instanceof CtLiteralImpl) {
                if (((CtUnaryOperatorImpl) op).getKind().toString().equals("NEG"))
                    string =  "(- "+((CtUnaryOperatorImpl) op).getOperand().toString()+")";
                else
                    string = ((CtUnaryOperatorImpl) op).getOperand().toString();
            } else if (((CtUnaryOperatorImpl) op).getOperand() instanceof CtInvocationImpl) {
                op = (CtInvocationImpl) ((CtUnaryOperatorImpl) op).getOperand();
                string = handleMethodInvocations(op);
                if(!string.isEmpty())
                    string = "(not " + handleMethodInvocations(op) + ")";
            } else {
                assertionEmpty = true;
                //System.out.println("culprit 1");
            }
        } else if(op instanceof CtArrayReadImpl) {
            CtArrayReadImpl arrayRead = (CtArrayReadImpl) op;
            CtVariableAccess variableAccess = arrayRead.getElements(new TypeFilter<CtVariableAccess>(CtVariableAccess.class){
                @Override
                public boolean matches(CtVariableAccess element) {
                    return true;
                }
            }).get(0);
            if(!variableAccess.getType().toString().startsWith("boolean") && arrayRead.getType() != null) {
                if (arrayRead.getIndexExpression() instanceof CtVariableReadImpl) {
                    string = variableAccess.toString() + "_" + arrayRead.getIndexExpression().toString();
                } else {
                    if (varIndexMap.containsKey(variableAccess.toString())) {
                        string = variableAccess.toString() + "_idx_" + varIndexMap.get(variableAccess.toString());
                    } else {
                        varIndexMap.put(variableAccess.toString(), index);
                        string = variableAccess.toString() + "_idx_" + (index++);
                    }
                }
                string = reshapeString(string);
                if(arrayRead.getType().toString().equals("double") || arrayRead.getType().toString().equals("byte")) {
                    variableInConstraint.add(new Pair<String, String>(string, "int"));
                } else {
                    variableInConstraint.add(new Pair<String, String>(string, arrayRead.getType().toString()));
                }
            }
        } else if(op instanceof CtInvocationImpl) {
            string = handleMethodInvocations(op);
        } else if(op instanceof CtVariableReadImpl) {
            if (((CtVariableReadImpl)op).getType() != null
                    && (((CtVariableReadImpl)op).getType().toString().equals("int")
                    || ((CtVariableReadImpl)op).getType().toString().equals("char")
                    || ((CtVariableReadImpl)op).getType().toString().equals("java.lang.String"))) {

                if(((CtVariableReadImpl)op).getType().toString().equals("char"))
                    CharAtFlag = true;

                string = op.toString();
                if(string.equals("count")) {
                    string = "count_var";
                }
                if(string.equals("len")) {
                    string = "len_var";
                }
                string = reshapeString(string);

                if(string.equals("charAt")) {
                    string = "charAtVar";
                }
                if(string.equals("lastIndexOf")) {
                    string = "lastIndexOfVar";
                }
                variableInConstraint.add(new Pair<String, String>(string, (((CtVariableReadImpl) op).getType().toString())));
//                if(((CtVariableReadImpl)op).getType().toString().equals("char")) {
//                    MethodInCondition = true;
//                }
            } else {
                assertionEmpty = true;
                //System.out.println("culprit 3");
            }
        } else if(op instanceof CtFieldReadImpl) {
            if (((CtFieldReadImpl)op).getVariable().getType() != null
                    && (((CtFieldReadImpl)op).getVariable().getType().toString().equals("int")
                    || ((CtFieldReadImpl)op).getVariable().getType().toString().equals("java.lang.String"))) {
                string = op.toString();
                if(string.equals("count")) {
                    string = "count_var";
                }
                if(string.equals("len")) {
                    string = "len_var";
                }
                string = reshapeString(string);
                variableInConstraint.add(new Pair<String, String>(string, (((CtFieldReadImpl) op).getType().toString())));
            }
            else if (((CtFieldReadImpl)op).getVariable().toString().equals("length")) {
                string = op.toString();
                string = reshapeString(string);
                variableInConstraint.add(new Pair<String, String>(string, "int"));
            }
            else {
                assertionEmpty = true;
                //System.out.println("culprit 4");
            }
        } else if (op instanceof  CtLiteralImpl) {
            if (((CtLiteralImpl) op).getValue() == null) {
                assertionEmpty = true;
                //System.out.println("culprit 5");
            } else if ((((CtLiteralImpl) op).getType().toString().equals("java.lang.object"))){
                assertionEmpty = true;
                //System.out.println("culprit 6");
            }else {
                string = op.toString();
                if(CharAtLGEQFlag && CharAtFlag && string.length() >= 3) {
                    int v = (int)string.toCharArray()[1];
                    string = ""+v;
                }
                else if(string.equals("'\"'")) {
                    if(!CharAtFlag)
                        string = ""+34;
                    else
                        string = "\"\\\"\"";
                }
                else if(string.equals("\'\\'\'")) {
                    if(!CharAtFlag)
                        string = ""+39;
                    else
                        string = "\"'\"";
                }
                else if(CharAtFlag) {
                    string = string.replace("'","\"");
                }
                else if(string.length() == 3 && string.contains("'") && !CharAtFlag  && !EqualFlag) {
                    int ascii = (int)(string.charAt(1));
                    string = ""+ascii;
                } else if(string.length() == 4 && string.contains("'") && !CharAtFlag && !EqualFlag) {
                    int ascii = (int)(string.charAt(2));
                    string = ""+ascii;
                }
            }
            if (((CtLiteralImpl)op).getType() != null && ((CtLiteralImpl)op).getType().toString().equals("int")) {
                int constant = 0;
                if(string.contains("0x") || string.contains("OX")) {
                    constant = 0;
                } else {
                    constant = Integer.parseInt(string);
                }
                if (constant > 10000)
                    string = "";
            }
        } else if (op instanceof CtTypeAccessImpl) {
            string = "\"stub\"";

        } else {
            string = "";
            assertionEmpty = true;
        }

        //special cases:
        string = string.replace("\\u001b", "u");
        string = string.replace("'", ":");
        string = string.replace("\"\"\"", "\":\"");
        return string;
    }

    private String generateAssertion(CtElement op, UnaryOperatorKind operator) {

        String assertionString = "";
        String string = "";

        //System.out.println(op.toString() + " -> " + op.getClass().toString());

        string = processOp(op);
        //System.out.println("String: " + string);

        if(string.equals(""))
            assertionEmpty = true;

        if(assertionEmpty) {
            assertionString = "";
            assertionEmpty = false;
        } else {
            switch (operator) {

                case NOT:
                    assertionString = "(not " + string + ")";
                    break;

                case NEG:
                    assertionString = "(- " + string + ")";
                    break;

                default:
                    break;
            }
        }

        return assertionString;
    }

    private String generateAssertion(CtElement leftOp, CtElement rightOp, BinaryOperatorKind operator) {

        if(operator == BinaryOperatorKind.GT || operator == BinaryOperatorKind.LT
                || operator == BinaryOperatorKind.GE || operator == BinaryOperatorKind.LE) {
            CharAtLGEQFlag = true;
        } else if(CharAtFlag == true && operator == BinaryOperatorKind.PLUS || operator == BinaryOperatorKind.MINUS) {
            CharAtLGEQFlag = true;
        } else {
            CharAtLGEQFlag = false;
        }

        String assertionString = "";
        String leftString = "";
        String rightString = "";

        //System.out.println(leftOp.toString() + " -> " + leftOp.getClass().toString());
        //System.out.println(rightOp.toString() + " -> " + rightOp.getClass().toString());

        if(rightOp.toString().contains("charAt"))
            CharAtFlag = true;

        leftString = processOp(leftOp);
        rightString = processOp(rightOp);

        if(leftOp instanceof CtVariableRead) {
            CtVariableRead varRead = (CtVariableRead)leftOp;
            if(varRead.getType() != null && varRead.getType().toString().equals("char")) {
                if (operator == BinaryOperatorKind.EQ || operator == BinaryOperatorKind.NE) {
                    leftString = "(charAt " + leftString + " 0)";
                    if (rightOp instanceof  CtLiteral) {
                        if (rightString.equals("'\\\\'")) {
                            rightString = "\"1\"";
                        }
                        if (!rightString.contains("\"")) {
                            rightString = "\"" + rightString + "\"";
                        }
                    } else if(rightOp instanceof CtVariableRead) {
                        CtVariableRead rightVarRead = (CtVariableRead) rightOp;
                        if (rightVarRead.getType().toString().equals("char")) {
                            if (operator == BinaryOperatorKind.EQ || operator == BinaryOperatorKind.NE) {
                                rightString = "(charAt " + rightString + " 0)";
                            }
                        }
                    }
                }
            }
            else if(varRead.getType() != null && varRead.getType().toString().equals("int")){
                if (rightString.equals("'\\n'")) {
                    rightString = "2";
                } else if (rightString.equals("'\\r'")) {
                    rightString = "3";
                }
            }
        }

        //System.out.println("Left String: " + leftString);
        //System.out.println("Right String: " + rightString);

        if(leftString.equals("") && rightString.equals(""))
            assertionEmpty = true;
        else if(leftString.equals("") || rightString.equals(""))
            if (operator == BinaryOperatorKind.AND || operator == BinaryOperatorKind.OR)
                assertionEmpty = false;
            else
                assertionEmpty = true;

        //System.out.println("assertionEmpty: " + assertionEmpty);

        if(assertionEmpty) {
            assertionString = "";
            assertionEmpty = false;
        } else {
            switch (operator) {

                case OR:
                    assertionString = "(or " + leftString + " " + rightString + ")";
                    break;

                case AND:
                    assertionString = "(and " + leftString + " " + rightString + ")";
                    break;

                case EQ:
                    assertionString = "(= " + leftString + " " + rightString + ")";
                    break;

                case NE:
                    assertionString = "(not (= " + leftString + " " + rightString + "))";
                    break;

                case GT:
                    assertionString = "(> " + leftString + " " + rightString + ")";
                    break;

                case LT:
                    assertionString = "(< " + leftString + " " + rightString + ")";
                    break;

                case GE:
                    assertionString = "(>= " + leftString + " " + rightString + ")";
                    break;

                case LE:
                    assertionString = "(<= " + leftString + " " + rightString + ")";
                    break;
                case PLUS:
                    assertionString = "(+ " + leftString + " " + rightString + ")";
                    break;
                case MINUS:
                    assertionString = "(- " + leftString + " " + rightString + ")";
                    break;
                case MUL:
                case DIV:
                case MOD:
                case BITAND:
                case BITOR:
                case BITXOR:
                    if (isNumeric(leftString) && isNumeric(rightString))
                        assertionString = "";
                    else if(isNumeric(leftString))
                        assertionString = rightString;
                    else
                        assertionString = leftString;
                    break;
                default:
                    break;
            }
        }

        return assertionString;
    }

    private boolean isNumeric(String s) {
        return s != null && s.matches("[-+]?\\d*\\.?\\d+");
    }

    private String postfix (String str){
        str = str.replace("(", "");
        str = str.replace(")", "");

        String op = "";

        if (str.contains("+")) {
            op = "\\+";
        } else if (str.contains("-")) {
            op = "-";
        } else if (str.contains("*")) {
            op = "*";
        } else if (str.contains("/")) {
            op = "/";
        } else {
            return str;
        }

        String p[] = str.split(op);
        String lop = p[0];
        String rop = p[1];

        return "(" + op + " " + lop + " " + rop + ")";
    }

    private String getRangeConstraintString(String sourceLocation, CtElement leftOp, CtElement rightOp) {
        String rangeConsAssertion = "";
        String varToReplaceInLeftOP = postfix(leftOp.toString());
        String varToReplaceInRightOP = postfix(rightOp.toString());
        ArrayList<String> intervalConsList = lineConsMap.get(sourceLocation);
        if (intervalConsList != null) {
            for (String intervalCon : intervalConsList) {
                if (intervalCon.contains("var1") && intervalCon.contains("var2")) {
                    String rangeCons = intervalCon.replaceAll("var1", varToReplaceInLeftOP);
                    rangeCons = rangeCons.replaceAll("var2", varToReplaceInRightOP);
                    rangeConsAssertion += "(assert " + rangeCons + ")\n";
                } else if (intervalCon.contains("var1") && !(leftOp instanceof CtLiteral)) {
                    String rangeCons = intervalCon.replaceAll("var1", varToReplaceInLeftOP);
                    rangeConsAssertion += "(assert " + rangeCons + ")\n";
                } else if (intervalCon.contains("var2") && !(rightOp instanceof CtLiteral)) {
                    String rangeCons = intervalCon.replaceAll("var2", varToReplaceInRightOP);
                    rangeConsAssertion += "(assert " + rangeCons + ")\n";
                }
            }
        }
        return rangeConsAssertion;
    }

    private String getRangeConstraint(String sourceLocation, CtElement leftOp, CtElement rightOp, BinaryOperatorKind operator) {
        String rangeConstraintString = "";
        if (operator == BinaryOperatorKind.AND || operator == BinaryOperatorKind.OR) {
            if ((leftOp instanceof CtBinaryOperatorImpl)) {
                CtBinaryOperatorImpl binaryOperator = (CtBinaryOperatorImpl) leftOp;

                CtElement newLeftOp = binaryOperator.getLeftHandOperand();
                CtElement newRightOp = binaryOperator.getRightHandOperand();
                rangeConstraintString += getRangeConstraintString(sourceLocation, newLeftOp, newRightOp);
            }
//            if ((rightOp instanceof CtBinaryOperatorImpl)) {
//                CtBinaryOperatorImpl binaryOperator = (CtBinaryOperatorImpl) rightOp;
//
//                CtElement newLeftOp = binaryOperator.getLeftHandOperand();
//                CtElement newRightOp = binaryOperator.getRightHandOperand();
//                rangeConstraintString += getRangeConstraintString(sourceLocation+"_2", newLeftOp, newRightOp);
//            }
        } else {
            rangeConstraintString = getRangeConstraintString(sourceLocation, leftOp, rightOp);
        }
        return rangeConstraintString;
    }

    private void handleMethodBlock(Launcher launcher, String ctClassQualifiedName, String currentMethodInfo, CtBlock methodBlock, String methodSign, String abstractDomain) {

        if(methodFeatureFlagMap.containsKey(currentMethodInfo)) {
            System.out.println("Why?");
            return;
        }

        String fileContent = "";
        ModelCounter modelCounter = new ModelCounter(31, "abc.linear_integer_arithmetic");
        //all features--------------------------------------------------
        int featureNumOfBranches = 0;
        int featureNumOfSelectiveBranches = 0;
        int featureMaxNumOfVarInBranches = 0;
        int featureAvgNumOfVarInBranches = 0;
        int featureAvgNumOfNestedBranches = 0;
        int featureMaxNumOfNestedBranches = 0;
        int featureNumOfBranchesSupportedByMC = 0;
        int featureNumberOfIfBranches = 0;
        int featureNumberOfLoopBranches = 0;
        int featureNumberOfSwitchCases = 0;
        int featureNumberOfBinaryOperations = 0;
        int featureNumberOfUnaryOperations = 0;
        int featureNumberOfMethodInvocations = 0;
        int numOfVars = 0;
        int numOfNests = 0;
        String condParent = "";
        String condEnv = "";
        //--------------------------------------------------------------

        if(methodBlock == null)
            return;
        List<CtIf> branchList = methodBlock.getElements(new TypeFilter<CtIf>(CtIf.class) {
            @Override
            public boolean matches(CtIf element) {
                return true;
            }
        });
        List<CtFor> forLoopBranchList = methodBlock.getElements(new TypeFilter<CtFor>(CtFor.class){
            @Override
            public boolean matches(CtFor element) {
                return true;
            }
        });
        List<CtWhile> whileLoopBranchList = methodBlock.getElements(new TypeFilter<CtWhile>(CtWhile.class){
            @Override
            public boolean matches(CtWhile element) {
                return true;
            }
        });
        List<CtDo> doWhileLoopBranchList = methodBlock.getElements(new TypeFilter<CtDo>(CtDo.class){
            @Override
            public boolean matches(CtDo element) {
                return true;
            }
        });
        List<CtSwitch> switchBranchList = methodBlock.getElements(new TypeFilter<CtSwitch>(CtSwitch.class){
            @Override
            public boolean matches(CtSwitch element) {
                return true;
            }
        });

        List<CtExpression> allConditionalExpression = new ArrayList<CtExpression>();

        for (CtIf cond : branchList) {
            allConditionalExpression.add(cond.getCondition());
            featureNumberOfIfBranches++;
        }
        for (CtFor cond : forLoopBranchList) {
            allConditionalExpression.add(cond.getExpression());
            featureNumberOfLoopBranches++;
        }
        for (CtWhile cond : whileLoopBranchList) {
            allConditionalExpression.add(cond.getLoopingExpression());
            featureNumberOfLoopBranches++;
        }
        for (CtDo cond : doWhileLoopBranchList) {
            allConditionalExpression.add(cond.getLoopingExpression());
            featureNumberOfLoopBranches++;
        }
        for (CtSwitch switchCase : switchBranchList) {
            List<CtCase> caseList = switchCase.getCases();
            CtExpression expr = switchCase.getSelector();
            for(CtCase cas : caseList) {
                if(cas.getCaseExpression() == null)
                    continue;
                featureNumberOfSwitchCases++;
                CtBinaryOperator binOP = launcher.getFactory().createBinaryOperator();
                binOP.setKind(BinaryOperatorKind.EQ);
                binOP.setLeftHandOperand(expr);
                binOP.setRightHandOperand(cas.getCaseExpression());
                CtIf ctif = launcher.getFactory().createIf();
                ctif.setCondition(binOP);
                binOP.setParent(ctif);
                ctif.setParent(cas);
                allConditionalExpression.add(ctif.getCondition());
            }
        }

        //System.out.println("Number of branches: " + allConditionalExpression.size());
        numberOfBranches += allConditionalExpression.size();
        featureNumOfBranches = allConditionalExpression.size();
        featureNumOfBranchesSupportedByMC = featureNumOfBranches;

        //numberOfBranchesWithLoop = numberOfBranches + forLoopBranchList.size() + whileLoopBranchList.size();

        for (CtExpression condExpr : allConditionalExpression) {

            if(condExpr == null)
                continue;

            if(condExpr.getParent() instanceof CtIf) {
                condParent = "I";
            } else if(condExpr.getParent() instanceof CtFor || condExpr.getParent() instanceof  CtWhile || condExpr.getParent() instanceof CtDo) {
                condParent = "L";
            }else if(condExpr.getParent() instanceof CtSwitch) {
                condParent = "S";
            }else {
                condParent = "X";
            }

            CtElement branchELem = condExpr.getParent();

            int numberOfNests = 1;
            while(branchELem.getParent() != null && !(branchELem.getParent() instanceof CtBlockImpl)) {
                branchELem = branchELem.getParent();
                numberOfNests++;
            }
            numOfNests += numberOfNests;

            if(numberOfNests > featureMaxNumOfNestedBranches)
                featureMaxNumOfNestedBranches = numberOfNests;



            if(condExpr.toString().contains("//"))
                continue;

            //Special case: ABC issue
            if(condExpr.toString().equals("(a - a) != 0"))
                continue;

            assertionEmpty = false;
            List<Pair<String,String>> model_counting_vars = new ArrayList<Pair<String,String>>();
            boolean countingModeStringFlag = false;
            MultiTrackIssueFlag = false;
            MethodInCondition = false;
            CharAtFlag = false;
            CharAtLGEQFlag = false;
            EqualFlag = false;
            varIndexMap = new HashMap<String, Integer>();
            //CtExpression condExpr = cond.getCondition();
            System.out.println(condExpr.toString());
            System.out.println(condExpr.getPosition());





            String modelCountingDomain = "";
            String modelCountingConstraint = "";

            SourcePosition sourcePosition = condExpr.getPosition();
            if(sourcePosition.toString().equals("(unknown file)"))
                sourcePosition = condExpr.getParent().getParent().getParent().getPosition();

            String[] temp = sourcePosition.toString().split("/");
            String sourceLocation = temp[temp.length-1].split("\\)")[0];

            if(condExpr.toString().equals("(!lFin.equals(com.puppycrawl.tools.checkstyle.checks.JavadocMethodCheck.NEXT_TAG)) && (!lFin.equals(com.puppycrawl.tools.checkstyle.checks.JavadocMethodCheck.END_JAVADOC))")) {
                System.out.println("here i am");
                fileContent += sourceLocation + "\t" + "0.999999" + "," + condParent + "," + condEnv + "," + "true" + "\n";
                continue;
            }

            if(condExpr.toString().equals("(!lFin.equals(com.puppycrawl.tools.checkstyle.checks.javadoc.JavadocMethodCheck.NEXT_TAG)) && (!lFin.equals(com.puppycrawl.tools.checkstyle.checks.javadoc.JavadocMethodCheck.END_JAVADOC))")) {
                System.out.println("here i am");
                fileContent += sourceLocation + "\t" + "0.999999" + "," + condParent + "," + condEnv + "," + "true" + "\n";
                continue;
            }

            if(condExpr.toString().equals("(!lFin.equals(com.puppycrawl.tools.checkstyle.checks.annotation.MissingDeprecatedCheck.NEXT_TAG)) && (!lFin.equals(com.puppycrawl.tools.checkstyle.checks.annotation.MissingDeprecatedCheck.END_JAVADOC))")) {
                System.out.println("here i am");
                fileContent += sourceLocation + "\t" + "0.999999" + "," + condParent + "," + condEnv + "," + "true" + "\n";
                continue;
            }

            if(condExpr.toString().equals("(!com.puppycrawl.tools.checkstyle.Main.PLAIN_FORMAT_NAME.equals(format)) && (!com.puppycrawl.tools.checkstyle.Main.XML_FORMAT_NAME.equals(format))")) {
                System.out.println("here i am");
                fileContent += sourceLocation + "\t" + "0.999999" + "," + condParent + "," + condEnv + "," + "true" + "\n";
                continue;
            }

            if (condExpr.toString().equals("line.contains(com.puppycrawl.tools.checkstyle.checks.javadoc.utils.InlineTagUtils.LINE_FEED) || line.contains(com.puppycrawl.tools.checkstyle.checks.javadoc.utils.InlineTagUtils.CARRIAGE_RETURN)")) {
                System.out.println("here i am");
                fileContent += sourceLocation + "\t" + "0.999999" + "," + condParent + "," + condEnv + "," + "true" + "\n";
                continue;
            }

            if (condExpr.toString().equals("((float) (a)) == 0.0")) {
                System.out.println("here i am");
                fileContent += sourceLocation + "\t" + "0.999999" + "," + condParent + "," + condEnv + "," + "true" + "\n";
                continue;
            }

            if (condExpr.toString().equals("line.contains(com.puppycrawl.tools.checkstyle.checks.javadoc.utils.InlineTagUtil.LINE_FEED) || line.contains(com.puppycrawl.tools.checkstyle.checks.javadoc.utils.InlineTagUtil.CARRIAGE_RETURN)")) {
                System.out.println("here i am");
                fileContent += sourceLocation + "\t" + "0.999999" + "," + condParent + "," + condEnv + "," + "true" + "\n";
                continue;
            }

            if (condExpr.toString().equals("class1.contains(separator) || class2.contains(separator)")) {
                System.out.println("here i am");
                fileContent += sourceLocation + "\t" + "0.999999" + "," + condParent + "," + condEnv + "," + "true" + "\n";
                continue;
            }

            if (condExpr.toString().equals("(((ch < 'a') || (ch > 'z')) && ((ch < 'A') && (ch > 'Z'))) && (ch != '_')")) {
                System.out.println("here i am");
                fileContent += sourceLocation + "\t" + "0.2" + "," + condParent + "," + condEnv + "," + "true" + "\n";
                continue;
            }

            if (condExpr.toString().equals("((!args[0].endsWith(\".jpg\")) && (!args[0].endsWith(\".tif\"))) && (!args[0].endsWith(\".gif\"))")) {
                System.out.println("here i am");
                fileContent += sourceLocation + "\t" + "0.8" + "," + condParent + "," + condEnv + "," + "true" + "\n";
                continue;
            }

            if (condExpr.toString().equals("(!s.startsWith(header)) && (!s.endsWith(footer))")) {
                System.out.println("here i am");
            }


            List<CtUnaryOperatorImpl> unaryOperatorList = condExpr.getElements(new TypeFilter<CtUnaryOperatorImpl>(CtUnaryOperatorImpl.class) {
                @Override
                public boolean matches(CtUnaryOperatorImpl candidate) {
                    return true;
                }
            });

            if ((condExpr instanceof CtUnaryOperatorImpl) && unaryOperatorList.size() > 0) {
                //System.out.println("unary condition: " + condExpr.toString());
                featureNumberOfUnaryOperations++;

                numberOfBranchesWithUnaryOp++;
                String rangeConsAssertion = "";

                CtUnaryOperatorImpl unaryOperator = unaryOperatorList.get(0);

                CtElement op = unaryOperator.getOperand();

                String assertionString = generateAssertion(op, unaryOperator.getKind());

                if(abstractDomain.equals("yes") && op instanceof CtBinaryOperatorImpl) {
                    CtBinaryOperatorImpl binOp = (CtBinaryOperatorImpl)op;
                    CtElement leftOp = binOp.getLeftHandOperand();
                    CtElement rightOp = binOp.getRightHandOperand();
                    rangeConsAssertion = getRangeConstraint(sourceLocation, leftOp, rightOp, binOp.getKind());
                }
                if (assertionString.contains("public"))
                    continue;

                if (!assertionString.equals("")) {
                    modelCountingConstraint += "(assert " + assertionString + ")\n";


                    System.out.println(variableInConstraint);

                    numOfVars += variableInConstraint.size();
                    if(variableInConstraint.size() > featureMaxNumOfVarInBranches)
                        featureMaxNumOfVarInBranches = variableInConstraint.size();

                    int numStringVars = 0;

                    for (Pair<String, String> var : variableInConstraint) {
                        //System.out.println(var.getKey() + ":" + var.getValue());
                        if (var.getValue().equals("int") || var.getValue().equals("long")) {
                            modelCountingConstraint = "(declare-fun " + var.getKey() + " () " + "Int" + ")\n" + modelCountingConstraint;
                            modelCountingDomain = "(declare-fun " + var.getKey() + " () " + "Int" + ")\n" + modelCountingDomain;

                            //String range = "(assert (and (>= " + var.getKey() + " 0) " + "(< " + var.getKey() + " 16)))\n";
                            //modelCountingConstraint += range;
                            //modelCountingDomain += range;

                            //modelCounter.setModelCountMode("abc.linear_integer_arithmetic");
                            //modelCounter.setBound(4);
                        } else if (var.getValue().equals("java.lang.String")) {
                            numStringVars++;
                            //String range = "/[ -~]{1,16}/";
                            //String range = "/[-0MCDXLVI]*/";
                            //String range_constraint = "(assert (in " + var.getKey() + " " + range.trim() + "))";
                            modelCountingConstraint = "(declare-fun " + var.getKey() + " () " + "String" + ")\n" + modelCountingConstraint;
                            modelCountingDomain = "(declare-fun " + var.getKey() + " () " + "String" + ")\n" + modelCountingDomain;
                            //modelCountingConstraint += range_constraint+"\n";
                            //modelCountingDomain += range_constraint+"\n";
                            countingModeStringFlag = true;
                            //modelCounter.setModelCountMode("abc.string");
                            //modelCounter.setBound(16);
                        }else if (var.getValue().equals("char")) {
//                                        String v = var.getKey();
//                                        String extra = "(assert (or " + " (= "+ v + " 45)" + "(= "+ v + " 48)" + "(= "+ v + " 77)" +
//                                                "(= "+ v + " 67)" + "(= "+ v + " 68)" + "(= "+ v + " 88)" +
//                                                "(= "+ v + " 76)" + "(= "+ v + " 86)" + "(= "+ v + " 73)" + "))\n";
                            modelCountingConstraint = "(declare-fun " + var.getKey() + " () " + "Int" + ")\n" + modelCountingConstraint;
                            modelCountingDomain = "(declare-fun " + var.getKey() + " () " + "Int" + ")\n" + modelCountingDomain;
                            String range = "(assert (and (>= " + var.getKey() + " 0) " + "(< " + var.getKey() + " 256)))\n";
                            modelCountingConstraint += range;
                            modelCountingDomain += range;
                            //modelCounter.setModelCountMode("abc.linear_integer_arithmetic");
                            //modelCounter.setBound(8);
                        }
                        model_counting_vars.add(new Pair<>(var.getKey(),var.getValue()));
                    }

                    if(numStringVars > 3) {
                        modelCountingConstraint = "";
                        continue;
                    }

                    if(numStringVars == variableInConstraint.size() && modelCountingConstraint.contains("+")) {
                        modelCountingConstraint = modelCountingConstraint.replaceAll(Pattern.quote("+"), "concat");
                    }

                    modelCountingDomain += rangeConsAssertion;
                    modelCountingConstraint += rangeConsAssertion;
                    modelCountingConstraint += "(check-sat)\n";
                    System.out.println(modelCountingConstraint);
                }
                variableInConstraint.clear();
            }


            List<CtBinaryOperatorImpl> binaryOperatorList = condExpr.getElements(new TypeFilter<CtBinaryOperatorImpl>(CtBinaryOperatorImpl.class) {
                @Override
                public boolean matches(CtBinaryOperatorImpl candidate) {
                    return true;
                }
            });

            if(unaryOperatorList.size() == 0 && binaryOperatorList.size() == 0){
                //System.out.println("Other conditions: " + condExpr.toString());
            }


            if ((condExpr instanceof CtBinaryOperatorImpl) && binaryOperatorList.size() > 0) {

                featureNumberOfBinaryOperations++;

                numberOfBranchesWithBinOp++;

                CtBinaryOperatorImpl binaryOperator = binaryOperatorList.get(0);

                CtElement leftOp = binaryOperator.getLeftHandOperand();
                CtElement rightOp = binaryOperator.getRightHandOperand();

                //System.out.println(leftOp);
                //System.out.println(rightOp);
                String rangeConsAssertion = "";

                if(abstractDomain.equals("yes")) {
                    rangeConsAssertion = getRangeConstraint(sourceLocation, leftOp, rightOp, binaryOperator.getKind());
                }

                String assertionString = "";

                if(rightOp == null)
                    System.out.println("here i am");

                if (rightOp.toString().equals("false")) {
                    assertionString = generateAssertion(leftOp,UnaryOperatorKind.NOT);
                }
                else{
                    assertionString = generateAssertion(leftOp, rightOp, binaryOperator.getKind());
                }

                if (assertionString.contains("0X") || assertionString.contains("0x"))
                    continue;
                if (assertionString.contains("0B"))
                    continue;
                if (assertionString.contains("public"))
                    continue;
                if (!assertionString.equals("")) {
                    if(assertionString.contains("charAt")) {
                        String patternToReplace = "\\(= \\(charAt ([a-zA-Z]+[0-9]*) (\\d+\\)) (\\d)(\\))";
                        if(assertionString.matches(patternToReplace)) {
                            String correctPattern = "\\(= \\(charAt $1 $2 \"$3\"$4";
                            assertionString = assertionString.replaceAll(patternToReplace, correctPattern);
                        }
                    }
                    modelCountingConstraint += "(assert " + assertionString + ")\n";

                    numOfVars += variableInConstraint.size();
                    if(variableInConstraint.size() > featureMaxNumOfVarInBranches)
                        featureMaxNumOfVarInBranches = variableInConstraint.size();

                    //System.out.println(variableInConstraint);
                    int numStringVars = 0;
                    int numCharVars = 0;
                    for (Pair<String, String> var : variableInConstraint) {
                        //System.out.println(var.getKey() + ":" + var.getValue());
                        if (var.getValue().equals("int") || var.getValue().equals("long")) {

                            if (modelCountingConstraint.contains("charAt") && modelCountingConstraint.contains(") " + var.getKey() + ")") && modelCountingConstraint.contains("(assert (=")) {
                                modelCountingConstraint = "(declare-fun " + var.getKey() + " () " + "String" + ")\n" + modelCountingConstraint;
                                modelCountingDomain = "(declare-fun " + var.getKey() + " () " + "String" + ")\n" + modelCountingDomain;
                                String range = "(assert (in " + var.getKey() + " /[ -~]{1,1}/))";
                                modelCountingConstraint += range;
                                modelCountingDomain += range;
                            } else {
                                modelCountingConstraint = "(declare-fun " + var.getKey() + " () " + "Int" + ")\n" + modelCountingConstraint;
                                modelCountingDomain = "(declare-fun " + var.getKey() + " () " + "Int" + ")\n" + modelCountingDomain;
                            }
                        } else if (var.getValue().equals("java.lang.String")) {
                            numStringVars++;
                            //String range = "/[ -~]{1,16}/";
                            //String range = "/[-0MCDXLVI]*/";
                            //String range_constraint = "(assert (in " + var.getKey() + " " + range.trim() + "))";
                            modelCountingConstraint = "(declare-fun " + var.getKey() + " () " + "String" + ")\n" + modelCountingConstraint;
                            modelCountingDomain = "(declare-fun " + var.getKey() + " () " + "String" + ")\n" + modelCountingDomain;
                            //modelCountingConstraint += range_constraint+"\n";
                            //modelCountingDomain += range_constraint+"\n";
                            countingModeStringFlag = true;
                            //modelCounter.setModelCountMode("abc.string");
                            //modelCounter.setBound(16);
                        }else if (var.getValue().equals("char")) {
                            numCharVars++;
//                                        String v = var.getKey();
//                                        String extra = "(assert (or " + " (= "+ v + " 45)" + "(= "+ v + " 48)" + "(= "+ v + " 77)" +
//                                                "(= "+ v + " 67)" + "(= "+ v + " 68)" + "(= "+ v + " 88)" +
//                                                "(= "+ v + " 76)" + "(= "+ v + " 86)" + "(= "+ v + " 73)" + "))\n";
                            if (!modelCountingConstraint.contains("charAt")) {
                                modelCountingConstraint = "(declare-fun " + var.getKey() + " () " + "Int" + ")\n" + modelCountingConstraint;
                                modelCountingDomain = "(declare-fun " + var.getKey() + " () " + "Int" + ")\n" + modelCountingDomain;
                                String range = "(assert (and (>= " + var.getKey() + " 0) " + "(< " + var.getKey() + " 256)))\n";
                                modelCountingConstraint += range;
                                modelCountingDomain += range;
                                //modelCounter.setModelCountMode("abc.linear_integer_arithmetic");
                                //modelCounter.setBound(8);
                            } else {
                                modelCountingConstraint = "(declare-fun " + var.getKey() + " () " + "String" + ")\n" + modelCountingConstraint;
                                modelCountingDomain = "(declare-fun " + var.getKey() + " () " + "String" + ")\n" + modelCountingDomain;
                                String range = "(assert (in " + var.getKey() + " /[ -~]{1,1}/))";
                                modelCountingConstraint += range;
                                modelCountingDomain += range;
                                //modelCounter.setModelCountMode("abc.linear_integer_arithmetic");
                                //modelCounter.setBound(8);
                            }
                        }
                        model_counting_vars.add(new Pair<>(var.getKey(),var.getValue()));
                    }

                    if(numCharVars > 0) { //special case to handle ABC issue for less than greater than with string
                        if ((modelCountingConstraint.contains("(= (charAt")) && (modelCountingConstraint.contains("(>") || modelCountingConstraint.contains("(<"))) {
                            modelCountingConstraint = "";
                            continue;
                        }
                    }
                    if(modelCountingConstraint.contains("startsWith") && modelCountingConstraint.contains("endsWith")) {
                        modelCountingConstraint = "";
                        continue;
                    }

                    if(numStringVars > 3) {
                        modelCountingConstraint = "";
                        continue;
                    }



                    if(numStringVars == variableInConstraint.size() && modelCountingConstraint.contains("+")) {
                        modelCountingConstraint = modelCountingConstraint.replaceAll(Pattern.quote("+"), "concat");
                    }

                    modelCountingDomain += rangeConsAssertion;
                    modelCountingConstraint += rangeConsAssertion;
                    modelCountingConstraint += "(check-sat)\n";
                    System.out.println(modelCountingConstraint);
                }

                variableInConstraint.clear();
            }

            List<CtInvocationImpl> methodInvocationList = condExpr.getElements(new TypeFilter<CtInvocationImpl>(CtInvocationImpl.class) {
                @Override
                public boolean matches(CtInvocationImpl candidate) {
                    return true;
                }
            });


            if ((condExpr instanceof CtInvocationImpl) && methodInvocationList.size() > 0) {

                featureNumberOfMethodInvocations++;

                numberOfBranchesWithmethodInvocation++;

                String assertionString = processOp(methodInvocationList.get(0));

                if (!assertionString.equals("")) {
                    modelCountingConstraint += "(assert " + assertionString + ")\n";

                    numOfVars += variableInConstraint.size();
                    if(variableInConstraint.size() > featureMaxNumOfVarInBranches)
                        featureMaxNumOfVarInBranches = variableInConstraint.size();

                    //System.out.println(variableInConstraint);
                    int numStringVarToCount = 0;
                    for (Pair<String, String> var : variableInConstraint) {
                        if (var.getKey().contains("\""))
                            continue;
                        //System.out.println(var.getKey() + ":" + var.getValue());
                        if (var.getValue().equals("int") || var.getValue().equals("long")) {
                            modelCountingConstraint = "(declare-fun " + var.getKey() + " () " + "Int" + ")\n" + modelCountingConstraint;
                            modelCountingDomain = "(declare-fun " + var.getKey() + " () " + "Int" + ")\n" + modelCountingDomain;
                            //String range = "(assert (and (>= " + var.getKey() + " 0) " + "(< " + var.getKey() + " 16)))\n";
                            //modelCountingConstraint += range;
                            //modelCountingDomain += range;
                            //modelCounter.setModelCountMode("abc.linear_integer_arithmetic");
                            //modelCounter.setBound(4);
                        } else if (var.getValue().equals("java.lang.String")) {
                            numStringVarToCount++;
                            //String range = "/[ -~]{1,16}/";
                            //String range = "/[-0MCDXLVI]*/";
                            //String range_constraint = "(assert (in " + var.getKey() + " " + range.trim() + "))";
                            modelCountingConstraint = "(declare-fun " + var.getKey() + " () " + "String" + ")\n" + modelCountingConstraint;
                            modelCountingDomain = "(declare-fun " + var.getKey() + " () " + "String" + ")\n" + modelCountingDomain;
                            //modelCountingConstraint += range_constraint + "\n";
                            //modelCountingDomain += range_constraint + "\n";
                            countingModeStringFlag = true;
                            //modelCounter.setModelCountMode("abc.string");
                            //modelCounter.setBound(16);
                        } else if (var.getValue().equals("char")) {
//                                        String v = var.getKey();
//                                        String extra = "(assert (or " + " (= "+ v + " 45)" + "(= "+ v + " 48)" + "(= "+ v + " 77)" +
//                                                "(= "+ v + " 67)" + "(= "+ v + " 68)" + "(= "+ v + " 88)" +
//                                                "(= "+ v + " 76)" + "(= "+ v + " 86)" + "(= "+ v + " 73)" + "))\n";
                            modelCountingConstraint = "(declare-fun " + var.getKey() + " () " + "Int" + ")\n" + modelCountingConstraint;
                            modelCountingDomain = "(declare-fun " + var.getKey() + " () " + "Int" + ")\n" + modelCountingDomain;
                            String range = "(assert (and (>= " + var.getKey() + " 0) " + "(< " + var.getKey() + " 256)))\n";
                            modelCountingConstraint += range;
                            modelCountingDomain += range;
                            //modelCounter.setModelCountMode("abc.linear_integer_arithmetic");
                            //modelCounter.setBound(8);
                        }
                        model_counting_vars.add(new Pair<>(var.getKey(),var.getValue()));
                    }

                    if (numStringVarToCount > 3) {
                        modelCountingConstraint = "";
                        continue;
                    }

                    if(numStringVarToCount == variableInConstraint.size() && modelCountingConstraint.contains("+")) {
                        modelCountingConstraint = modelCountingConstraint.replaceAll(Pattern.quote("+"), "concat");
                    }


                    modelCountingConstraint += "(check-sat)\n";
                    System.out.println(modelCountingConstraint);
                }

                variableInConstraint.clear();
            }


            double prob_true, prob_false;
            if(modelCountingConstraint.equals("")) {
                System.err.println("This branch is not considered for model counting! Fifty fifty selectivity!");
                featureNumOfBranchesSupportedByMC--;

                if(condExpr.toString().contains("null")) {
                    condEnv = "N";
                } else if(condExpr instanceof CtInvocationImpl) {
                    condEnv = "M";
                }else {
                    condEnv = "O";
                }

                fileContent += sourceLocation + "\t" + "0.5" + "," + condParent + "," + condEnv + ",false\n";
            } else {
                condEnv = "O";
                try {

                    //temporary fix for mutitrack issue
                    if(model_counting_vars.size() == 2) {
                        String eqAssertion = "(assert (= " + model_counting_vars.get(0) + " " + model_counting_vars.get(1) + ")";
                        if(modelCountingConstraint.contains(eqAssertion)) {
                            MultiTrackIssueFlag = true;
                        }
                    }

                    if (modelCountingConstraint.contains("assert") && !modelCountingConstraint.contains("define") &&
                            !modelCountingConstraint.contains("declare-fun"))
                        continue;

                    BigDecimal cons_count = modelCounter.getModelCount(modelCountingConstraint, model_counting_vars, MultiTrackIssueFlag);
                    System.out.println("Branch model count: " + cons_count);

                    modelCountingDomain += "(assert true)\n";
                    modelCountingDomain += "(check-sat)";
                    System.out.println(modelCountingDomain);
                    BigDecimal dom_count = modelCounter.getModelCount(modelCountingDomain, model_counting_vars, false);
                    System.out.println("Branch domain count:" + dom_count);

                    prob_true = cons_count.doubleValue() / dom_count.doubleValue();
                    if(prob_true == 1.0)
                        prob_true = 0.9999999999;
                    if(prob_true == 0.0)
                        prob_true = 0.0000000001;
                    prob_false = 1.0 - prob_true;

                    System.out.println("True branch probability: " + prob_true);
                    System.out.println("False branch probability: " + prob_false);

                    numberOfBranchesConsidered++;
                    boolean selectiveBranch = false;
                    if (prob_true < 0.05 || prob_false < 0.05) {
                        //System.err.println("This branch is selective");
                        selectiveBranch = true;
                        numberOfSelectiveBranches++;
                        featureNumOfSelectiveBranches++;
                        Pair<String, String> classMethodPair = new Pair<String, String>(ctClassQualifiedName, methodSign);
                        if (selectiveBranchMap.containsKey(classMethodPair)) {
                            selectiveBranchMap.put(classMethodPair, selectiveBranchMap.get(classMethodPair) + 1);
                        } else {
                            selectiveBranchMap.put(classMethodPair, 1);
                        }
                    } else {
                        //System.err.println("This branch is not selective");
                    }
                    if(MethodInCondition) {
                        fileContent += sourceLocation + "\t" + prob_false + "," + condParent + "," + condEnv + "," + selectiveBranch +"\n";
                    } else {
                        fileContent += sourceLocation + "\t" + prob_true + "," + condParent + "," + condEnv + "," + selectiveBranch + "\n";
                    }
                } catch (Exception ex) {
                    //System.err.println("Not appropriate constraint to count models");
                }
            }

            featureAvgNumOfVarInBranches = numOfVars/featureNumOfBranches;
            featureAvgNumOfNestedBranches = numOfNests/featureNumOfBranches;
        }

//                    String featureString = currentMethodInfo + "," +
//                            featureNumOfBranches + "," +
//                            featureNumberOfIfBranches + "," +
//                            featureNumberOfLoopBranches + "," +
//                            featureNumberOfSwitchCases + "," +
//                            featureNumberOfUnaryOperations + "," +
//                            featureNumberOfBinaryOperations + "," +
//                            featureNumberOfMethodInvocations + "," +
//                            featureMaxNumOfVarInBranches + "," +
//                            featureAvgNumOfVarInBranches + "," +
//                            featureNumOfBranchesSupportedByMC + "," +
//                            featureAvgNumOfNestedBranches + "," +
//                            featureNumOfSelectiveBranches + "\n";



        methodFeatureFlagMap.put(currentMethodInfo, true);
        String featureString = methodFeatureMap.get(currentMethodInfo) + "," +
                featureNumOfBranches + "," +
                featureNumOfSelectiveBranches + "," +
                featureNumberOfMethodInvocations + "," +
                (featureNumOfBranches - featureNumOfBranchesSupportedByMC) + "," +
                featureMaxNumOfVarInBranches + "," +
                featureMaxNumOfNestedBranches +
                "\n";

        try {
            bwFeature.write(featureString);
            bw.write(fileContent);
        } catch(IOException ex) {
            ex.printStackTrace();
        }
    }

    private String getChangedType(String type) {
        String updatedType=type;

        if(type.contains(".")) {
            updatedType = "L" + type.substring(type.lastIndexOf(".")+1) + ";";
        }
        else {
            updatedType = updatedType.replace("int", "I");
            updatedType = updatedType.replace("float", "F");
            updatedType = updatedType.replace("double", "D");
            updatedType = updatedType.replace("long", "J");
            updatedType = updatedType.replace("short", "S");
            updatedType = updatedType.replace("char", "C");
            updatedType = updatedType.replace("byte", "B");
            updatedType = updatedType.replace("boolean", "Z");
            updatedType = updatedType.replace("void", "V");
        }

        long count = updatedType.chars().filter(ch -> ch == '[').count();
        //count += updatedType.chars().filter(ch -> ch == ']').count();
        String paren = "";
        for(int c = 0; c < count; c++) {
            paren += "[";
        }
        updatedType = updatedType.replace("[]", "");
        updatedType = paren + updatedType;

        /*if (updatedType.contains("[[[[D")) {
            updatedType = updatedType.replace("[[[[D", "[[[D");
        } else if (updatedType.contains("[[D")) {
            updatedType = updatedType.replace("[[D", "[D");
        }

        if (updatedType.contains("[[[[I")) {
            updatedType = updatedType.replace("[[[[I", "[[[I");
        } else if (updatedType.contains("[[I")) {
            updatedType = updatedType.replace("[[I", "[I");
        }

        if (updatedType.contains("[[[[B")) {
            updatedType = updatedType.replace("[[[[B", "[[[B");
        } else if (updatedType.contains("[[B")) {
            updatedType = updatedType.replace("[[B", "[B");
        }*/

        return updatedType;
    }

    private String getConstructorSignature(CtConstructor constructor) {
        String sign = constructor.getSimpleName();
        sign += "(";

        long count = constructor.getReference().getType().toString().chars().filter(ch -> ch == '[').count();
        //count += updatedType.chars().filter(ch -> ch == ']').count();
        String returnParen = "";
        for(int c = 0; c < count; c++) {
            returnParen += "[";
        }

        List<CtParameter> methodParams = constructor.getParameters();

        String params = "";
        for(CtParameter param : methodParams) {
            String paramType = param.getType().toString();
            paramType = getChangedType(paramType);
            params += paramType;
        }
        if((constructor.isPrivate() || constructor.isPublic() || constructor.isProtected()) && params.startsWith("[") || params.startsWith("I") || params.startsWith("D") || params.startsWith("F") || params.startsWith("B")) {
            sign += returnParen;
        }
        sign += params;
        sign += ")";
        //sign += getChangedType(method.getReference().getType().toString());

        return sign;
    }

    private String getMethodSignature(CtMethod method) {
        String sign = method.getSimpleName();
        sign += "(";

        long count = method.getReference().getType().toString().chars().filter(ch -> ch == '[').count();
        //count += updatedType.chars().filter(ch -> ch == ']').count();
        String returnParen = "";
        for(int c = 0; c < count; c++) {
            returnParen += "[";
        }

        List<CtParameter> methodParams = method.getParameters();

        String params = "";
        for(CtParameter param : methodParams) {
            String paramType = param.getType().toString();
            paramType = getChangedType(paramType);
            params += paramType;
        }
        if((method.isPrivate() || method.isPublic() || method.isProtected()) && params.startsWith("[") || params.startsWith("I") || params.startsWith("D") || params.startsWith("F") || params.startsWith("B")) {
            sign += returnParen;
        }
        sign += params;
        sign += ")";
        //sign += getChangedType(method.getReference().getType().toString());

        return sign;
    }

    private void handleCLasses(Launcher launcher, String classFile, List<CtType<?>> ctClasslist, String abstractDomain) {
        for (CtType<?> ctType : ctClasslist) {
            numberOfClasses++;

            Set<CtConstructor> curConstList = new HashSet<>();
            Set<CtMethod> curMethodList = new HashSet<>();
            String currentMethodInfo = "";

            if (ctType instanceof CtClass) {
                CtClass ctClass = (CtClass) ctType;

                curConstList.addAll(ctClass.getConstructors());
                curMethodList.addAll(ctClass.getAllMethods());

                for (CtConstructor<?> constructor : curConstList) {
                    numberOfMethods++;

                    System.out.println(constructor.getSimpleName());

                    String constSign = getConstructorSignature(constructor);
                    System.out.println(constSign);

                    // to collect only necessary method info
                    currentMethodInfo = ctClass.getQualifiedName() + ":" + constSign;

                    if (!methodList.contains(currentMethodInfo)) {
                        if(currentMethodInfo.contains("$")) {
                            String origMethodName = currentMethodInfo.split("\\$")[1].split(":")[0];
                            currentMethodInfo = currentMethodInfo.replace("<init>", origMethodName);
                            if (!methodList.contains(currentMethodInfo)) {
                                System.out.println(currentMethodInfo);
                                continue;
                            }
                        } else {
                            int idx = currentMethodInfo.lastIndexOf(".");
                            String classPart = currentMethodInfo.substring(0,idx+1);
                            String methodPart = currentMethodInfo.substring(idx+1);
                            String classFileName = classFile.substring(classFile.lastIndexOf("/")+1).split(".java")[0];
                            classPart += classFileName;
                            currentMethodInfo = classPart + "$" + methodPart;
                            System.out.println(currentMethodInfo);

                            String origMethodName = currentMethodInfo.split("\\$")[1].split(":")[0];
                            currentMethodInfo = currentMethodInfo.replace("<init>", origMethodName);

                            if (!methodList.contains(currentMethodInfo)) {
                                System.out.println(currentMethodInfo);
                                continue;
                            }
                        }

                    }


                    CtBlock constBlock = constructor.getBody();
                    handleMethodBlock(launcher, ctClass.getQualifiedName(), currentMethodInfo, constBlock, constructor.getSignature(), abstractDomain);
                }

                System.out.println(ctClass.getQualifiedName());


                for (CtMethod<?> method : curMethodList) {
                    numberOfMethods++;
                    System.out.println(method.getSimpleName());

                    String methodSign = getMethodSignature(method);
                    System.out.println(methodSign);

                    // to collect only necessary method info
                    currentMethodInfo = ctClass.getQualifiedName() + ":" + methodSign;

                    if (!methodList.contains(currentMethodInfo)) {
                        int idx = currentMethodInfo.lastIndexOf(".");
                        String classPart = currentMethodInfo.substring(0,idx+1);
                        String methodPart = currentMethodInfo.substring(idx+1);
                        String classFileName = classFile.substring(classFile.lastIndexOf("/")+1).split(".java")[0];
                        classPart += classFileName;
                        currentMethodInfo = classPart + "$" + methodPart;
                        System.out.println(currentMethodInfo);
                        if (!methodList.contains(currentMethodInfo)) {
                            continue;
                        }
                    }


                    CtBlock methodBlock = method.getBody();
                    handleMethodBlock(launcher, ctClass.getQualifiedName(), currentMethodInfo, methodBlock, method.getSignature(), abstractDomain);
                }

                Set<CtType<?>> innerClassSet  = ctClass.getNestedTypes();
                List<CtType<?>> innerClassList = innerClassSet.stream().collect(Collectors.toList());
                handleCLasses(launcher,classFile,innerClassList,abstractDomain);
            }

            else if (ctType instanceof CtInterface) {
                CtInterface ctInterface = (CtInterface) ctType;

                curMethodList = ctInterface.getAllMethods();
                for (CtMethod<?> method : curMethodList) {
                    numberOfMethods++;
                    System.out.println(method.getSimpleName());

                    String methodSign = getMethodSignature(method);
                    System.out.println(methodSign);

                    // to collect only necessary method info
                    currentMethodInfo = ctInterface.getQualifiedName() + ":" + methodSign;

                    if (!methodList.contains(currentMethodInfo)) {
                        System.out.println(currentMethodInfo);
                        continue;
                    }


                    CtBlock methodBlock = method.getBody();
                    handleMethodBlock(launcher, ctInterface.getQualifiedName(), currentMethodInfo, methodBlock, method.getSignature(), abstractDomain);
                }
            }
        }
    }

    public void runBranchSelectivityForAClass(String classFile, String abstractDomain) {

        //test purpose
        //CtClass ctClass = Launcher.parseClass("class A { void m() { System.out.println(\"yeah\");} void n() { System.out.println(\"yeah\");} }");
        //System.out.println(ctClass.getMethods().size());

        try {

            if (classFile.contains("$")) {
                classFile = classFile.substring(0, classFile.indexOf("$"));
            }
            System.out.println(classFile);

            if(classFile.contains("StackoverflowError"))
                return;

            Launcher launcher = new Launcher();
            launcher.addInputResource(classFile);
            launcher.buildModel();

            List<CtType<?>> ctClasslist = launcher.getFactory().Class().getAll();
            //System.out.println("Number of classes: " + ctClasslist.size());

            handleCLasses(launcher, classFile, ctClasslist,abstractDomain);

        } catch(Exception ex) {
            ex.printStackTrace();
        }
    }

    public void processAllJavaFiles(String projectDirectory, String abstractDomain) {
        try {
            File dir = new File(projectDirectory);
            String[] extensions = new String[]{"java"};
            List<File> files = (List<File>) FileUtils.listFiles(dir, extensions, true);
            sourceDirectory = projectDirectory;

            if(abstractDomain.equals("yes"))
                readIntervalAnalysisResults();


            File bfile = new  File(sourceDirectory+"/branch_probability.txt");
            if (!bfile.exists()) {
                bfile.createNewFile();
            }

            FileWriter fw = new FileWriter(bfile.getAbsoluteFile());
            bw = new BufferedWriter(fw);


            for (File file : files) {
                //System.out.println("file: " + file.getAbsolutePath());
                String filePath = file.getAbsolutePath();
//                if (filePath.endsWith("Generator.java") || filePath.contains("Test.java"))
//                    continue;
                runBranchSelectivityForAClass(filePath, abstractDomain);
            }
            bw.close();
        } catch (Exception ex) {
            System.err.println("Can not process java files from the given directory: " + projectDirectory);
        }
    }

    public void printProjectInfo() {
        System.out.println("Number of classes: " + numberOfClasses);
        System.out.println("Number of methods: " + numberOfMethods);
        System.out.println("Number of branches with loop: " + numberOfBranchesWithLoop);
        System.out.println("Number of branches: " + numberOfBranches);
        System.out.println("Number of branches with method invocation: " + numberOfBranchesWithmethodInvocation);
        System.out.println("Number of branches with unary operation: " + numberOfBranchesWithUnaryOp);
        System.out.println("Number of branches with binary operation: " + numberOfBranchesWithBinOp);
        System.out.println("Number of considered branches: " + numberOfBranchesConsidered);
        System.out.println("Number of selective branches: " + numberOfSelectiveBranches);

        double percentageOfSelectiveBranches = 100.0 * numberOfSelectiveBranches/numberOfBranches;
        System.out.println("Percentage of selective branches: " + String.format("%.2f",percentageOfSelectiveBranches) + "%");

        System.out.println("----------------------------------------------------");
        System.out.println("Class Name\tMethod Name\tNumber of Selective Branches");
        for (Map.Entry<Pair<String,String>, Integer> entry : selectiveBranchMap.entrySet()) {
            System.out.println(entry.getKey().getKey()+"\t"+entry.getKey().getValue()+"\t"+entry.getValue());
        }
    }

    public static void main(String args[]) {
        //System.out.println("Branch Selectivity starts ...");
        BranchSelectivity branchSelectivity = new BranchSelectivity();
        sourceDirectory = args[0];
        long startTime = System.currentTimeMillis();

        //---------------------------------------------------------------------------

        try {
            File bfile = new File(sourceDirectory + "/branch_selectivity_feature.csv");
            if (!bfile.exists()) {
                bfile.createNewFile();
            }

            FileWriter fw = new FileWriter(bfile.getAbsoluteFile());
            bwFeature = new BufferedWriter(fw);
//            bwFeature.write("method,numOfBranches," +
//                    "numbOfIf,numOfLoop,numberOfSwitchCases" +
//                    "numOfUnaryOP,numOfBinOp,numOfMethodInvocation," +
//                    "maxNumOfVarInBranches,avgNumOfVarsInBranches," +
//                    "numOfBrancesSupportedByMC," +
//                    "avgNumberOfNestedBranches," +
//                    "numOfSelectiveBranches\n");
            //bwFeature.write("method,numOfConditionals,numOfSelectiveConditionals\n");
        } catch(IOException e) {
            e.printStackTrace();
        }

        //---------------------------------------------------------------------------
        //Additional code for extracting code metric features from PReach
        String codeMetricsFile = args[2];
        File file = new File(codeMetricsFile);
        try {
            BufferedReader br = new BufferedReader(new FileReader(file));

            String st;
            while ((st = br.readLine()) != null) {
//                if(st.startsWith("ID,method"))
//                    continue;
//                String methodInfo = st.split(",")[1];
//                methodList.add(methodInfo);
                if(st.contains("DEFECTIVE")) {
                    bwFeature.write(st + ",NOB,NOSB,NOBMI,NOBNMC,MNVB,MNNB\n");
                    continue;
                }
                String methodInfo = st.split(",")[2];
                methodInfo = methodInfo.replace(" ",":");
                //int idx = methodInfo.lastIndexOf("(");
                //methodInfo = methodInfo.substring(0,idx);

//                if(methodInfo.contains("$")) {
//                    if(methodInfo.contains("ActionListener") || methodInfo.contains("ItemListener") ||
//                            methodInfo.contains("ChangeListener") || methodInfo.contains("Comparator") ||
//                            methodInfo.contains("PageLoader") || methodInfo.contains("JScrollPane") ||
//                            methodInfo.contains("Runnable") || methodInfo.contains("ArrayDataSource") ||
//                            methodInfo.contains("JButton")) {
//                        String part[] = methodInfo.split(":");
//                        methodInfo = part[0].split("\\$")[0] + ":" + part[1];
//                        System.out.println("hi!");
//                    }
//                    else {
//                        int id1 = methodInfo.lastIndexOf("$");
//                        String mainClass = methodInfo.substring(id1 + 1);
//                        methodInfo = methodInfo.substring(0, id1);
//                        int id2 = methodInfo.lastIndexOf(".");
//                        methodInfo = methodInfo.substring(0, id2 + 1) + mainClass;
//                    }
//                }

                methodList.add(methodInfo);
                if(methodFeatureMap.containsKey(methodInfo)) {
                    System.out.println(methodInfo);
                    System.out.print("Why??");
                }
                methodFeatureMap.put(methodInfo,st);

                //Classes that are not an inner class but in the same java file
//                String part[] = methodInfo.split(":");
//                methodInfo = part[0].split("\\$")[0] + ":" + part[1];
//                methodList.add(methodInfo);
//                methodFeatureMap.put(methodInfo,st);
            }
        } catch (IOException e) {
            e.printStackTrace();
        }




        branchSelectivity.processAllJavaFiles(sourceDirectory, args[1]);

        for (Map.Entry mapElement : methodFeatureMap.entrySet()) {
            String key = (String)mapElement.getKey();
            if(!methodFeatureFlagMap.containsKey(key)) {
                String featureString = methodFeatureMap.get(key) + "," +
                        "-1" + "," +
                        "-1" + "," +
                        "-1" + "," +
                        "-1" + "," +
                        "-1" + "," +
                        "-1" + "\n";

                try {
                    bwFeature.write(featureString);
                } catch(IOException ex) {
                    ex.printStackTrace();
                }
            }
        }

        try {
            bwFeature.close();
        } catch (IOException e) {
            e.printStackTrace();
        }

        long endTime = System.currentTimeMillis();
        int processTime = (int) ((endTime-startTime) * 0.001);
        System.out.println("----------------------------------------------------");
        System.out.println("Total processing time: " + processTime + " seconds");
        System.out.println("----------------------------------------------------");
        //branchSelectivity.printProjectInfo();
    }
}