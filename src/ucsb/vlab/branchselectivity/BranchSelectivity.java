package ucsb.vlab.branchselectivity;

import com.martiansoftware.util.StringUtils;
import vlab.cs.ucsb.edu.ModelCounter;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Properties;
import java.util.Set;
import java.lang.String;
import java.math.BigDecimal;

import javafx.util.Pair;

import org.apache.commons.io.FileUtils;

import java.io.BufferedWriter;
import java.io.FileWriter;

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
    public static Map<String, Integer> varIndexMap;

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

    private String processOp(CtElement op) {
        String string = "";

        if(op instanceof CtBinaryOperatorImpl) {
            //System.out.println("Processing CtBinaryOperatorImpl");
            assertionEmpty = false;
            CtBinaryOperatorImpl binOp = ((CtBinaryOperatorImpl) op);
            string = generateAssertion(binOp.getLeftHandOperand(),binOp.getRightHandOperand(),binOp.getKind());
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
            if(arrayRead.getIndexExpression() instanceof CtVariableReadImpl) {
                string = variableAccess.toString() + "_" + arrayRead.getIndexExpression().toString();
            } else {
                if(varIndexMap.containsKey(variableAccess.toString())) {
                    string = variableAccess.toString() + "_idx_" + varIndexMap.get(variableAccess.toString());
                } else {
                    varIndexMap.put(variableAccess.toString(), index);
                    string = variableAccess.toString() + "_idx_" + (index++);
                }
            }
            variableInConstraint.add(new Pair<String,String>(string,arrayRead.getType().toString()));
        } else if(op instanceof CtInvocationImpl) {
            CtInvocationImpl invocationImpl = (CtInvocationImpl) op;

            //write code to handle all string operations
            System.out.println(invocationImpl.getExecutable().getDeclaringType());
            if(invocationImpl.getExecutable().getType() != null && (invocationImpl.getExecutable().getType().toString().equals("int")
                    || invocationImpl.getExecutable().getType().toString().equals("java.lang.String"))) {

                if (invocationImpl.getExecutable().getDeclaringType().toString().equals("java.lang.String")
                    && invocationImpl.getExecutable().getSimpleName().equals("length")) {
                    String var = invocationImpl.getTarget().toString().replace("[","").replace("]","");
                    variableInConstraint.add(new Pair<String, String>(var, invocationImpl.getExecutable().getDeclaringType().toString()));
                    string = "(len " + var +")";
                } else {
                    string = op.toString().replaceAll("[^a-zA-Z0-9]", "");
                    variableInConstraint.add(new Pair<String, String>(string, invocationImpl.getExecutable().getType().toString()));
                }
            } else if(invocationImpl.getExecutable().getType() != null && (invocationImpl.getExecutable().getType().toString().equals("boolean")
                    || invocationImpl.getExecutable().getType().toString().equals("char"))
                && (invocationImpl.getExecutable().getDeclaringType().toString().equals("java.lang.String"))
                    || (invocationImpl.getExecutable().getDeclaringType().toString().equals("java.lang.CharSequence"))
                    || (invocationImpl.getExecutable().getDeclaringType().toString().equals("java.lang.Character")
                    || invocationImpl.getExecutable().getDeclaringType().toString().equals("char") )) {

                if(invocationImpl.getTarget().toString().contains("toString()")) {
                    assertionEmpty = true;
                }

                else if (invocationImpl.getExecutable().getSimpleName().equals("equals")) {
                    String param = processOp((CtElement) invocationImpl.getArguments().get(0));
                    variableInConstraint.add(new Pair<String, String>(invocationImpl.getTarget().toString(), invocationImpl.getExecutable().getDeclaringType().toString()));

                    if (invocationImpl.getExecutable().getDeclaringType().toString().equals("char")) {
                        if (param.length() == 3 && param.contains("'") && !CharAtFlag) {
                            int ascii = (int) (param.charAt(1));
                            param = "" + ascii;
                        }
                    }

                    string = "(= " + invocationImpl.getTarget().toString() + " " + param +")";
                }

                else if (invocationImpl.getExecutable().getSimpleName().equals("isDigit")) {
                    String param = processOp((CtElement) invocationImpl.getArguments().get(0));
                    variableInConstraint.add(new Pair<String, String>(invocationImpl.getTarget().toString(), invocationImpl.getExecutable().getDeclaringType().toString()));
                    string = "(and (>= " + param + " 48)" + "(<= " + param + " 57))";
                }

                else if (invocationImpl.getExecutable().getSimpleName().equals("contains")) {
                    String param = processOp((CtElement) invocationImpl.getArguments().get(0));
                    variableInConstraint.add(new Pair<String, String>(invocationImpl.getTarget().toString(), invocationImpl.getExecutable().getDeclaringType().toString()));
                    param = param.replace("\"", "\"(\"");
                    string = "(contains " + invocationImpl.getTarget().toString() + " " + param +")";
                }

                else if (invocationImpl.getExecutable().getSimpleName().equals("startsWith")) {
                    String param = processOp((CtElement) invocationImpl.getArguments().get(0));
                    variableInConstraint.add(new Pair<String, String>(invocationImpl.getTarget().toString(), invocationImpl.getExecutable().getDeclaringType().toString()));
                    param = param.replace("\"", "\"(\"");
                    string = "(startsWith " + invocationImpl.getTarget().toString() + " \"" + param +"\" )";
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
                    String param = processOp((CtElement) invocationImpl.getArguments().get(0));

                    if(CharAtLGEQFlag) {
                        if(invocationImpl.getExecutable().getDeclaringType().toString().equals("java.lang.CharSequence")) {
                            variableInConstraint.add(new Pair<String, String>(invocationImpl.getTarget().toString(), "char" ));
                        } else {
                            variableInConstraint.add(new Pair<String, String>(invocationImpl.getTarget().toString(), "char"));
                        }
                        string = invocationImpl.getTarget().toString();
                    } else {
                        if (invocationImpl.getExecutable().getDeclaringType().toString().equals("java.lang.CharSequence")) {
                            variableInConstraint.add(new Pair<String, String>(invocationImpl.getTarget().toString(), "java.lang.String"));
                        } else {
                            variableInConstraint.add(new Pair<String, String>(invocationImpl.getTarget().toString(), invocationImpl.getExecutable().getDeclaringType().toString()));
                        }
                        string = "(charAt " + invocationImpl.getTarget().toString() + " " + param + ")";
                    }


//                    try {
//                        Double.parseDouble(param);
//                    } catch(NumberFormatException e){
//                        System.err.println("Not numeric!!!");
//                        variableInConstraint.add(new Pair<String, String>(param, "int"));
//                    }
                }


            } else {
                assertionEmpty = true;
                //System.out.println("culprit 2");
            }
        } else if(op instanceof CtVariableReadImpl) {
            if (((CtVariableReadImpl)op).getType() != null
                    && (((CtVariableReadImpl)op).getType().toString().equals("int")
                    || ((CtVariableReadImpl)op).getType().toString().equals("char")
                    || ((CtVariableReadImpl)op).getType().toString().equals("java.lang.String"))) {
                string = op.toString();
                if(string.equals("count")) {
                    string = "count_var";
                }
                if(string.equals("len")) {
                    string = "len_var";
                }
                string = string.replace(".", "");
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
                string = string.replace(".", "");
                variableInConstraint.add(new Pair<String, String>(string, (((CtFieldReadImpl) op).getType().toString())));
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
                if(CharAtLGEQFlag && CharAtFlag) {
                    int v = (int)string.toCharArray()[1];
                    string = ""+v;
                }
                else if(string.equals("\'\\'\'")) {
                    if(!CharAtFlag)
                        string = ""+39;
                    else
                        string = "\"'\"";
                } else if(CharAtFlag) {
                    string = string.replace("'","\"");
                } else if(string.length() == 3 && string.contains("'") && !CharAtFlag) {
                    int ascii = (int)(string.charAt(1));
                    string = ""+ascii;
                }
            }
        } else {
            string = "";
            assertionEmpty = true;
        }
//        if(string.length() == 3 && string.contains("'")) {
//            int ascii = (int)(string.charAt(1));
//            string = ""+ascii;
//        }


        return string;
    }

    private String generateAssertion(CtElement op, UnaryOperatorKind operator) {

         String assertionString = "";
        String string = "";

        System.out.println(op.toString() + " -> " + op.getClass().toString());

        string = processOp(op);
        System.out.println("String: " + string);

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
        } else {
            CharAtLGEQFlag = false;
        }

        String assertionString = "";
        String leftString = "";
        String rightString = "";

        //System.out.println(leftOp.toString() + " -> " + leftOp.getClass().toString());
        //System.out.println(rightOp.toString() + " -> " + rightOp.getClass().toString());

        leftString = processOp(leftOp);
        rightString = processOp(rightOp);

        //System.out.println("Left String: " + leftString);
        //System.out.println("Right String: " + rightString);

        if(leftString.equals("") && rightString.equals(""))
            assertionEmpty = true;
        else if (operator == BinaryOperatorKind.AND || operator == BinaryOperatorKind.OR)
            assertionEmpty = false;

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
                    assertionString = leftString;
                    break;
                default:
                    break;
            }
        }

        return assertionString;
    }

    public void runBranchSelectivityForAClass(String classFile) {

        //test purpose
        //CtClass ctClass = Launcher.parseClass("class A { void m() { System.out.println(\"yeah\");} void n() { System.out.println(\"yeah\");} }");
        //System.out.println(ctClass.getMethods().size());

        try {
            String fileContent = "";
            ModelCounter modelCounter = new ModelCounter(31, "abc.linear_integer_arithmetic");

            if (classFile.contains("$")) {
                classFile = classFile.substring(0, classFile.indexOf("$"));
            }
            System.out.println(classFile);

            Launcher launcher = new Launcher();
            launcher.addInputResource(classFile);
            launcher.buildModel();

            List<CtType<?>> ctClasslist = launcher.getFactory().Class().getAll();
            System.out.println("Number of classes: " + ctClasslist.size());

            for (CtType<?> ctClass : ctClasslist) {
                System.out.println("Class Name: " + ctClass.getQualifiedName());
                numberOfClasses++;

                //if(!ctClass.getSimpleName().equals("CharSequenceUtils"))
                //    continue;

                for (CtMethod<?> method : ctClass.getMethods()) {
                    System.out.println("Method Name: " + method.getSimpleName());
                    numberOfMethods++;

                    //if(!method.getSimpleName().equals("regionMatches"))
                    //    continue;

                    CtBlock methodBlock = method.getBody();
                    if(methodBlock == null)
                        continue;
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

                    System.out.println("Number of branches: " + branchList.size());
                    numberOfBranches += branchList.size();

                    numberOfBranchesWithLoop = numberOfBranches + forLoopBranchList.size() + whileLoopBranchList.size();

                    for (CtIf cond : branchList) {
                        assertionEmpty = false;
                        List<String> model_counting_vars = new ArrayList<String>();
                        boolean countingModeStringFlag = false;
                        MultiTrackIssueFlag = false;
                        MethodInCondition = false;
                        CharAtFlag = false;
                        varIndexMap = new HashMap<String, Integer>();
                        CtExpression condExpr = cond.getCondition();
                        System.out.println(condExpr.toString());
                        System.out.println(condExpr.getPosition());

                        String modelCountingDomain = "";
                        String modelCountingConstraint = "";

//                        List<CtVariableAccess> varList = condExpr.getElements(new TypeFilter<CtVariableAccess>(CtVariableAccess.class) {
//                            @Override
//                            public boolean matches(CtVariableAccess element) {
//                                return true;
//                            }
//                        });
//                    Set<CtVariableAccess> varSet = new HashSet<CtVariableAccess>();
//                    for (CtVariableAccess var : varList) {
//                        if(!varSet.contains(var)) {
//                            varSet.add(var);
//                            System.out.println(var.getVariable() + ":" + var.getType());
//                            if(var.getType() == null)
//                                continue;
//                            else if(var.getType().toString().equals("int")) {
//                                modelCountingConstraint += "(declare-fun " + var.getVariable() + " () " + "Int" + ")\n";
//                                modelCountingDomain += "(declare-fun " + var.getVariable() + " () " + "Int" + ")\n";
//                            }
//                            else if(var.getType().toString().equals("java.lang.String")) {
//                                modelCountingConstraint += "(declare-fun " + var.getVariable() + " () " + "String" + ")\n";
//                                modelCountingDomain += "(declare-fun " + var.getVariable() + " () " + "String" + ")\n";
//                            }
//                        }
//                    }

                        List<CtUnaryOperatorImpl> unaryOperatorList = condExpr.getElements(new TypeFilter<CtUnaryOperatorImpl>(CtUnaryOperatorImpl.class) {
                            @Override
                            public boolean matches(CtUnaryOperatorImpl candidate) {
                                return true;
                            }
                        });

                        if ((condExpr instanceof CtUnaryOperatorImpl) && unaryOperatorList.size() > 0) {
                            System.out.println("unary condition: " + condExpr.toString());
                            numberOfBranchesWithUnaryOp++;

                            CtUnaryOperatorImpl unaryOperator = unaryOperatorList.get(0);

                            CtElement op = unaryOperator.getOperand();

                            String assertionString = generateAssertion(op, unaryOperator.getKind());

                            if (!assertionString.equals("")) {
                                modelCountingConstraint += "(assert " + assertionString + ")\n";


                                //System.out.println(variableInConstraint);

                                for (Pair<String, String> var : variableInConstraint) {
                                    System.out.println(var.getKey() + ":" + var.getValue());
                                    if (var.getValue().equals("int") || var.getValue().equals("long")) {
                                        modelCountingConstraint = "(declare-fun " + var.getKey() + " () " + "Int" + ")\n" + modelCountingConstraint;
                                        modelCountingDomain = "(declare-fun " + var.getKey() + " () " + "Int" + ")\n" + modelCountingDomain;

                                        //String range = "(assert (and (>= " + var.getKey() + " 0) " + "(< " + var.getKey() + " 16)))\n";
                                        //modelCountingConstraint += range;
                                        //modelCountingDomain += range;

                                        //modelCounter.setModelCountMode("abc.linear_integer_arithmetic");
                                        //modelCounter.setBound(4);
                                    } else if (var.getValue().equals("java.lang.String")) {
                                        String range = "/[ -~]{1,16}/";
                                        //String range = "/[-0MCDXLVI]*/";
                                        String range_constraint = "(assert (in " + var.getKey() + " " + range.trim() + "))";
                                        modelCountingConstraint = "(declare-fun " + var.getKey() + " () " + "String" + ")\n" + modelCountingConstraint;
                                        modelCountingDomain = "(declare-fun " + var.getKey() + " () " + "String" + ")\n" + modelCountingDomain;
                                        modelCountingConstraint += range_constraint+"\n";
                                        modelCountingDomain += range_constraint+"\n";
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
                                    model_counting_vars.add(var.getKey());
                                }

//                                if(countingModeStringFlag) {
//                                    modelCounter.setModelCountMode("abc.string");
//                                } else {
//                                    modelCounter.setModelCountMode("abc.linear_integer_arithmetic");
//                                }


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
                            System.out.println("Other conditions: " + condExpr.toString());
                        }


                        if ((condExpr instanceof CtBinaryOperatorImpl) && binaryOperatorList.size() > 0) {

                            numberOfBranchesWithBinOp++;

                            CtBinaryOperatorImpl binaryOperator = binaryOperatorList.get(0);

                            CtElement leftOp = binaryOperator.getLeftHandOperand();
                            CtElement rightOp = binaryOperator.getRightHandOperand();

                            String assertionString = generateAssertion(leftOp, rightOp, binaryOperator.getKind());

                            if (!assertionString.equals("")) {
                                modelCountingConstraint += "(assert " + assertionString + ")\n";


                                //System.out.println(variableInConstraint);

                                for (Pair<String, String> var : variableInConstraint) {
                                    System.out.println(var.getKey() + ":" + var.getValue());
                                    if (var.getValue().equals("int") || var.getValue().equals("long")) {
                                        modelCountingConstraint = "(declare-fun " + var.getKey() + " () " + "Int" + ")\n" + modelCountingConstraint;
                                        modelCountingDomain = "(declare-fun " + var.getKey() + " () " + "Int" + ")\n" + modelCountingDomain;

                                        //String range = "(assert (and (>= " + var.getKey() + " 0) " + "(< " + var.getKey() + " 16)))\n";
                                        //modelCountingConstraint += range;
                                        //modelCountingDomain += range;

                                        //modelCounter.setModelCountMode("abc.linear_integer_arithmetic");
                                        //modelCounter.setBound(4);
                                    } else if (var.getValue().equals("java.lang.String")) {
                                        String range = "/[ -~]{1,16}/";
                                        //String range = "/[-0MCDXLVI]*/";
                                        String range_constraint = "(assert (in " + var.getKey() + " " + range.trim() + "))";
                                        modelCountingConstraint = "(declare-fun " + var.getKey() + " () " + "String" + ")\n" + modelCountingConstraint;
                                        modelCountingDomain = "(declare-fun " + var.getKey() + " () " + "String" + ")\n" + modelCountingDomain;
                                        modelCountingConstraint += range_constraint+"\n";
                                        modelCountingDomain += range_constraint+"\n";
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
                                        String range = "(assert (and (>= " + var.getKey() + " 0) " + "(< " + var.getKey() + " 16)))\n";
                                        modelCountingConstraint += range;
                                        modelCountingDomain += range;
                                        //modelCounter.setModelCountMode("abc.linear_integer_arithmetic");
                                        //modelCounter.setBound(8);
                                    }
                                    model_counting_vars.add(var.getKey());
                                }


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

                            numberOfBranchesWithmethodInvocation++;

                            String assertionString = processOp(methodInvocationList.get(0));

                            if (!assertionString.equals("")) {
                                modelCountingConstraint += "(assert " + assertionString + ")\n";


                                //System.out.println(variableInConstraint);

                                for (Pair<String, String> var : variableInConstraint) {
                                    System.out.println(var.getKey() + ":" + var.getValue());
                                    if (var.getValue().equals("int") || var.getValue().equals("long")) {
                                        modelCountingConstraint = "(declare-fun " + var.getKey() + " () " + "Int" + ")\n" + modelCountingConstraint;
                                        modelCountingDomain = "(declare-fun " + var.getKey() + " () " + "Int" + ")\n" + modelCountingDomain;
                                        String range = "(assert (and (>= " + var.getKey() + " 0) " + "(< " + var.getKey() + " 16)))\n";
                                        modelCountingConstraint += range;
                                        modelCountingDomain += range;
                                        //modelCounter.setModelCountMode("abc.linear_integer_arithmetic");
                                        //modelCounter.setBound(4);
                                    } else if (var.getValue().equals("java.lang.String")) {
                                        String range = "/[ -~]{1,16}/";
                                        //String range = "/[-0MCDXLVI]*/";
                                        String range_constraint = "(assert (in " + var.getKey() + " " + range.trim() + "))";
                                        modelCountingConstraint = "(declare-fun " + var.getKey() + " () " + "String" + ")\n" + modelCountingConstraint;
                                        modelCountingDomain = "(declare-fun " + var.getKey() + " () " + "String" + ")\n" + modelCountingDomain;
                                        modelCountingConstraint += range_constraint+"\n";
                                        modelCountingDomain += range_constraint+"\n";
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
                                    model_counting_vars.add(var.getKey());
                                }


                                modelCountingConstraint += "(check-sat)\n";
                                System.out.println(modelCountingConstraint);
                            }

                            variableInConstraint.clear();
                        }

                        String[] temp = condExpr.getPosition().toString().split("/");
                        String sourceLocation = temp[temp.length-1].split("\\)")[0];

                        double prob_true, prob_false;
                        if(modelCountingConstraint.equals("")) {
                            System.err.println("This branch is not considered");
                            fileContent += sourceLocation + "\t" + "0.5" + "\n";
                        } else {
                            try {

                                //temporary fix for mutitrack issue
                                if(model_counting_vars.size() == 2) {
                                    String eqAssertion = "(assert (= " + model_counting_vars.get(0) + " " + model_counting_vars.get(1) + ")";
                                  if(modelCountingConstraint.contains(eqAssertion)) {
                                      MultiTrackIssueFlag = true;
                                  }
                                }

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
                                if (prob_true < 0.05 || prob_false < 0.05) {
                                    System.err.println("This branch is selective");
                                    numberOfSelectiveBranches++;
                                    Pair<String, String> classMethodPair = new Pair<String, String>(ctClass.getQualifiedName(), method.getSignature());
                                    if (selectiveBranchMap.containsKey(classMethodPair)) {
                                        selectiveBranchMap.put(classMethodPair, selectiveBranchMap.get(classMethodPair) + 1);
                                    } else {
                                        selectiveBranchMap.put(classMethodPair, 1);
                                    }
                                } else {
                                    System.err.println("This branch is not selective");
                                }
                                if(MethodInCondition) {
                                    fileContent += sourceLocation + "\t" + prob_false + "\n";
                                } else {
                                    fileContent += sourceLocation + "\t" + prob_true + "\n";
                                }
                                //fileContent += sourceLocation + "\t" + prob_true + "\n";
                            } catch (Exception ex) {
                                System.err.println("Not appropriate constraint to count models");
                                //fileContent += sourceLocation + "\t" + "X" + "\n";
                            }
                        }
                    }
                }
            }
            System.out.println(fileContent);
            bw.write(fileContent);
        } catch(Exception ex) {
            ex.printStackTrace();
        }
    }

    public void processAllJavaFiles(String projectDirectory) {
        try {
            File dir = new File(projectDirectory);
            String[] extensions = new String[]{"java"};
            List<File> files = (List<File>) FileUtils.listFiles(dir, extensions, true);
            sourceDirectory = projectDirectory;



            File bfile = new  File(sourceDirectory+"/branch_probability.txt");
            if (!bfile.exists()) {
                bfile.createNewFile();
            }

            FileWriter fw = new FileWriter(bfile.getAbsoluteFile());
            bw = new BufferedWriter(fw);


            for (File file : files) {
                System.out.println("file: " + file.getAbsolutePath());
                runBranchSelectivityForAClass(file.getAbsolutePath());
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
        System.out.println("Branch Selectivity starts ...");
        BranchSelectivity branchSelectivity = new BranchSelectivity();
        long startTime = System.currentTimeMillis();
        branchSelectivity.processAllJavaFiles(args[0]);
        long endTime = System.currentTimeMillis();
        int processTime = (int) ((endTime-startTime) * 0.001);
        System.out.println("----------------------------------------------------");
        System.out.println("Total processing time: " + processTime + " seconds");
        System.out.println("----------------------------------------------------");
        branchSelectivity.printProjectInfo();
    }
}