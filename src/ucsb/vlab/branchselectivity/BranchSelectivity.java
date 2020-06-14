package ucsb.vlab.branchselectivity;

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

    private static Set<Pair<String,String>> variableInConstraint = new HashSet<Pair<String,String>>();
    private static int index = 0;

    private boolean assertionEmpty = false;

    private int numberOfClasses = 0;
    private int numberOfMethods = 0;
    private int numberOfBranches = 0;
    private int numberOfSelectiveBranches = 0;

    private long processingTime;

    private String processOp(CtElement op) {
        String string = "";

        if(op instanceof CtBinaryOperatorImpl) {
            CtBinaryOperatorImpl binOp = ((CtBinaryOperatorImpl) op);
            string = generateAssertion(binOp.getLeftHandOperand(),binOp.getRightHandOperand(),binOp.getKind());
        } else if (op instanceof CtUnaryOperatorImpl) {
            if (((CtUnaryOperatorImpl) op).getOperand() instanceof CtBinaryOperatorImpl) {
                CtBinaryOperatorImpl binOp = ((CtBinaryOperatorImpl) ((CtUnaryOperatorImpl) op).getOperand());
                string = "(not" + generateAssertion(binOp.getLeftHandOperand(), binOp.getRightHandOperand(), binOp.getKind()) + ")";
            } else if (((CtUnaryOperatorImpl) op).getOperand() instanceof CtLiteralImpl) {
                if (((CtUnaryOperatorImpl) op).getKind().toString().equals("NEG"))
                    string =  "(- "+((CtUnaryOperatorImpl) op).getOperand().toString()+")";
                else
                    string = ((CtUnaryOperatorImpl) op).getOperand().toString();
            } else {
                assertionEmpty = true;
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
                string = variableAccess.toString() + "_idx_" + (index++);
            }
            variableInConstraint.add(new Pair<String,String>(string,arrayRead.getType().toString()));
        } else if(op instanceof CtInvocationImpl) {
            CtInvocationImpl invocationImpl = (CtInvocationImpl) op;
            if(invocationImpl.getExecutable().getType() == null) {
                assertionEmpty = true;
            } else {
                string = op.toString().replaceAll("[^a-zA-Z0-9]", "");
                variableInConstraint.add(new Pair<String, String>(string, invocationImpl.getExecutable().getType().toString()));
            }
        } else if(op instanceof CtVariableReadImpl) {
            if (((CtVariableReadImpl)op).getType() != null) {
                string = op.toString();
                variableInConstraint.add(new Pair<String, String>(string, (((CtVariableReadImpl) op).getType().toString())));
            } else
                assertionEmpty = true;
        } else if(op instanceof CtFieldReadImpl) {
            if (((CtFieldReadImpl)op).getType() != null) {
                string = op.toString();
                variableInConstraint.add(new Pair<String, String>(string, (((CtFieldReadImpl) op).getType().toString())));
            }
            else
                assertionEmpty = true;
        } else if (op instanceof  CtLiteralImpl) {
            if (((CtLiteralImpl) op).getValue() == null) {
                assertionEmpty = true;
            } else {
                string = op.toString();
            }
        } else {
            string = op.toString();
        }

        return string;
    }

    private String generateAssertion(CtElement leftOp, CtElement rightOp, BinaryOperatorKind operator) {

        String assertionString = "";
        String leftString = "";
        String rightString = "";

        //System.out.println(leftOp.toString() + leftOp.getClass().toString());
        //System.out.println(rightOp.toString() + rightOp.getClass().toString());

        leftString = processOp(leftOp);
        rightString = processOp(rightOp);

        if(leftString.equals("") && rightString.equals(""))
            assertionEmpty = true;

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

                for (CtMethod<?> method : ctClass.getMethods()) {
                    System.out.println("Method Name: " + method.getSimpleName());
                    numberOfMethods++;

                    CtBlock methodBlock = method.getBody();
                    List<CtIf> branchList = methodBlock.getElements(new TypeFilter<CtIf>(CtIf.class) {
                        @Override
                        public boolean matches(CtIf element) {
                            return true;
                        }
                    });
//                List<CtFor> forLoopBranchList = methodBlock.getElements(new TypeFilter<CtFor>(CtFor.class){
//                    @Override
//                    public boolean matches(CtFor element) {
//                        return true;
//                    }
//                });
//                List<CtWhile> whileLoopBranchList = methodBlock.getElements(new TypeFilter<CtWhile>(CtWhile.class){
//                    @Override
//                    public boolean matches(CtWhile element) {
//                        return true;
//                    }
//                });

                    System.out.println("Number of branches: " + branchList.size());
                    numberOfBranches += branchList.size();

                    for (CtIf cond : branchList) {
                        CtExpression condExpr = cond.getCondition();
                        System.out.println(condExpr.toString());
                        System.out.println(condExpr.getPosition());

                        String modelCountingDomain = "";
                        String modelCountingConstraint = "";

                        List<CtVariableAccess> varList = condExpr.getElements(new TypeFilter<CtVariableAccess>(CtVariableAccess.class) {
                            @Override
                            public boolean matches(CtVariableAccess element) {
                                return true;
                            }
                        });
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

                        List<CtBinaryOperatorImpl> binaryOperatorList = condExpr.getElements(new TypeFilter<CtBinaryOperatorImpl>(CtBinaryOperatorImpl.class) {
                            @Override
                            public boolean matches(CtBinaryOperatorImpl candidate) {
                                return true;
                            }
                        });

                        if (binaryOperatorList.size() > 0) {
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
                                    } else if (var.getValue().equals("java.lang.String")) {
                                        modelCountingConstraint = "(declare-fun " + var.getKey() + " () " + "String" + ")\n" + modelCountingConstraint;
                                        modelCountingDomain = "(declare-fun " + var.getKey() + " () " + "String" + ")\n" + modelCountingDomain;
                                    }
                                }


                                modelCountingConstraint += "(check-sat)\n";
                                System.out.println(modelCountingConstraint);

                                BigDecimal cons_count = modelCounter.getModelCount(modelCountingConstraint);
                                System.out.println("Branch model count: " + cons_count);

                                modelCountingDomain += "(assert true)\n";
                                modelCountingDomain += "(check-sat)";
                                BigDecimal dom_count = modelCounter.getModelCount(modelCountingDomain);
                                System.out.println("Branch domain count:" + dom_count);

                                double prob_true = cons_count.doubleValue() / dom_count.doubleValue();
                                double prob_false = 1.0 - prob_true;

                                if (prob_true < 0.05 || prob_false < 0.05) {
                                    System.err.println("This branch is selective");
                                    numberOfSelectiveBranches++;
                                }
                            }

                            variableInConstraint.clear();
                        }
                    }
                }
            }
        } catch(Exception ex) {
            ex.printStackTrace();
        }

    }

    public void processAllJavaFiles(String projectDirectory) {
        try {
            File dir = new File(projectDirectory);
            String[] extensions = new String[]{"java"};
            List<File> files = (List<File>) FileUtils.listFiles(dir, extensions, true);
            for (File file : files) {
                System.out.println("file: " + file.getAbsolutePath());
                runBranchSelectivityForAClass(file.getAbsolutePath());
            }
        } catch (Exception ex) {
            System.err.println("Can not process java files from the given directory: " + projectDirectory);
        }
    }

    public void printProjectInfo() {
        System.out.println("Number of classes: " + numberOfClasses);
        System.out.println("Number of methods: " + numberOfMethods);
        System.out.println("Number of branches: " + numberOfBranches);
        System.out.println("Number of selective branches: " + numberOfSelectiveBranches);

        double percentageOfSelectiveBranches = 100.0 * numberOfSelectiveBranches/numberOfBranches;
        System.out.println("Percentage of selective branches: " + String.format("%.2f",percentageOfSelectiveBranches) + "%");
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