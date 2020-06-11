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

    private String generateAssertion(CtElement leftOp, CtElement rightOp, BinaryOperatorKind operator) {

        String assertionString = "";
        String leftString = "";
        String rightString = "";

        System.out.println(leftOp.toString() + leftOp.getClass().toString());
        System.out.println(rightOp.toString() + rightOp.getClass().toString());

        if(leftOp instanceof CtBinaryOperatorImpl) {
            CtBinaryOperatorImpl binOp = ((CtBinaryOperatorImpl) leftOp);
            leftString = generateAssertion(binOp.getLeftHandOperand(),binOp.getRightHandOperand(),binOp.getKind());
        } else if(leftOp instanceof CtArrayReadImpl) {
            CtArrayReadImpl arrayRead = (CtArrayReadImpl) leftOp;
            CtVariableAccess variableAccess = arrayRead.getElements(new TypeFilter<CtVariableAccess>(CtVariableAccess.class){
                @Override
                public boolean matches(CtVariableAccess element) {
                    return true;
                }
            }).get(0);
            if(arrayRead.getIndexExpression() instanceof CtVariableReadImpl) {
                leftString = variableAccess.toString() + "_" + arrayRead.getIndexExpression().toString();
            } else {
                leftString = variableAccess.toString() + "_idx_" + (index++);
            }
            variableInConstraint.add(new Pair<String,String>(leftString,arrayRead.getType().toString()));
        } else {
            leftString = leftOp.toString();
            variableInConstraint.add(new Pair<String,String>(leftString,(((CtVariableRead)leftOp).getType().toString())));
        }

        if(rightOp instanceof CtBinaryOperatorImpl) {
            CtBinaryOperatorImpl binOp = ((CtBinaryOperatorImpl) rightOp);
            rightString = generateAssertion(binOp.getLeftHandOperand(),binOp.getRightHandOperand(),binOp.getKind());
        } else if(rightOp instanceof CtArrayReadImpl) {
            CtArrayReadImpl arrayRead = (CtArrayReadImpl) rightOp;
            CtVariableAccess variableAccess = arrayRead.getElements(new TypeFilter<CtVariableAccess>(CtVariableAccess.class){
                @Override
                public boolean matches(CtVariableAccess element) {
                    return true;
                }
            }).get(0);
            if(arrayRead.getIndexExpression() instanceof CtVariableReadImpl) {
                rightString = variableAccess.toString() + "_" + arrayRead.getIndexExpression().toString();
            } else {
                rightString = variableAccess.toString() + "_idx_" + (index++);
            }
            variableInConstraint.add(new Pair<String,String>(rightString,arrayRead.getType().toString()));
        } else {
            rightString = rightOp.toString();
            variableInConstraint.add(new Pair<String,String>(rightString,(((CtVariableRead)rightOp).getType().toString())));
        }

        switch(operator) {

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

        return assertionString;
    }

    public void runBranchSelectivityForAClass(String classFile) {

        //test purpose
        //CtClass ctClass = Launcher.parseClass("class A { void m() { System.out.println(\"yeah\");} void n() { System.out.println(\"yeah\");} }");
        //System.out.println(ctClass.getMethods().size());

        ModelCounter modelCounter = new ModelCounter(31, "abc.linear_integer_arithmetic");

        if(classFile.contains("$")){
            classFile = classFile.substring(0, classFile.indexOf("$"));
        }
        System.out.println(classFile);

        Launcher launcher = new Launcher();
        launcher.addInputResource(classFile);
        launcher.buildModel();

        List<CtType<?>> ctClasslist = launcher.getFactory().Class().getAll();
        System.out.println("Number of classes: " + ctClasslist.size());

        for(CtType<?> ctClass : ctClasslist) {
            System.out.println("Class Name: " + ctClass.getQualifiedName());

            for(CtMethod<?> method : ctClass.getMethods()) {
                System.out.println("Method Name: " + method.getSimpleName());
                CtBlock methodBlock = method.getBody();
                List<CtIf> branchList = methodBlock.getElements(new TypeFilter<CtIf>(CtIf.class){
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

                        modelCountingConstraint += "(assert " + generateAssertion(leftOp, rightOp, binaryOperator.getKind()) + ")\n";

                        //System.out.println(variableInConstraint);

                        for (Pair<String,String> var : variableInConstraint) {
                            System.out.println(var.getKey() + ":" + var.getValue());
                            if(var.getValue().equals("int")) {
                                modelCountingConstraint = "(declare-fun " + var.getKey() + " () " + "Int" + ")\n" + modelCountingConstraint;
                                modelCountingDomain = "(declare-fun " + var.getKey() + " () " + "Int" + ")\n" + modelCountingDomain;
                            }
                            else if(var.getValue().equals("java.lang.String")) {
                                modelCountingConstraint = "(declare-fun " + var.getKey() + " () " + "String" + ")\n" + modelCountingConstraint;
                                modelCountingDomain = "(declare-fun " + var.getKey() + " () " + "String" + ")\n" + modelCountingDomain;
                            }
                        }


                        modelCountingConstraint += "(check-sat)\n";
                        System.out.println(modelCountingConstraint);

                        variableInConstraint.clear();

                        BigDecimal cons_count = modelCounter.getModelCount(modelCountingConstraint);
                        System.out.println("Branch model count: " + cons_count);

                        modelCountingDomain += "(assert true)\n";
                        modelCountingDomain += "(check-sat)";
                        BigDecimal dom_count = modelCounter.getModelCount(modelCountingDomain);
                        System.out.println("Branch domain count:" + dom_count);

                        double prob_true = cons_count.doubleValue()/dom_count.doubleValue();
                        double prob_false = 1.0 - prob_true;

                        if(prob_true < 0.05 || prob_false < 0.05) {
                            System.out.println("This branch is selective");
                        }
                    }
                }
            }
        }

    }

    public static void main(String args[]) {
        System.out.println("Branch Selectivity starts ...");
        BranchSelectivity branchSelectivity = new BranchSelectivity();
        branchSelectivity.runBranchSelectivityForAClass(args[0]);
    }
}