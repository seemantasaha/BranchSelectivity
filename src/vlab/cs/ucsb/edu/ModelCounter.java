package vlab.cs.ucsb.edu;

import vlab.cs.ucsb.edu.DriverProxy.Option;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import javafx.util.Pair;

//import edu.ucsb.cs.vlab.translate.smtlib.from.abc.ABCTranslator;


public class ModelCounter {

  DriverProxy abc;
  int bound;
  BigInteger total_model_count;
  String model_count_mode;

  public ModelCounter(int bound, String mode) {
    this.abc = new DriverProxy();
    //this.abc.setOption(Option.USE_UNSIGNED_INTEGERS);
    this.abc.setOption(DriverProxy.Option.DISABLE_EQUIVALENCE_CLASSES);
    this.bound = bound;
    this.total_model_count = new BigInteger("0");
    this.model_count_mode = mode;
  }

  public void setBound(int bound) {
    this.bound = bound;
  }

  public void setModelCountMode(String mode) {
    this.model_count_mode = mode;
  }

  public BigDecimal getModelCount(String PCTranslation, List<Pair<String,String>> model_counting_vars, boolean multiTrackissueFlag) {



    long startTime = System.nanoTime();
    boolean result = abc.isSatisfiable(PCTranslation);
    long endTime = System.nanoTime();

    System.out.println("Constraint solving time: " + (endTime - startTime) / 1000000000.0);

    BigDecimal count = new BigDecimal(0);;
    if (result) {
//      startTime = System.nanoTime();
//      if (this.model_count_mode.equals("abc.string")) {
//        count = new BigDecimal(abc.countStrs((long) bound));
//      } else if (this.model_count_mode.equals("abc.linear_integer_arithmetic")) {
//        double MIN = (-1) * Math.pow(2, bound);
//        double MAX = Math.pow(2, bound) - 1;
//
//        if (MIN >= 0) {
//          abc.setOption(Option.USE_UNSIGNED_INTEGERS);
//        }
//        count = new BigDecimal(abc.countInts((long) bound));
//      }

//      count = new BigDecimal(1);
//      if(multiTrackissueFlag) {
//        count = new BigDecimal(abc.countVariable(model_counting_vars.get(0), bound));
//      } else {
//        for (String var_name : model_counting_vars) {
//          if(var_name.equals("java.lang.Character"))
//            continue;
//          count = count.multiply(new BigDecimal(abc.countVariable(var_name, bound)));
//        }
//      }

      int numIntVar = 0, numStringVar = 0;
      if (model_counting_vars.size() > 1) {
        for(Pair<String,String> var : model_counting_vars) {
          if(var.getValue().equals("java.lang.String"))
            numStringVar++;
          else
            numIntVar++;
        }
      }

      if(model_counting_vars.size() > 1 && numStringVar == 0) {
        count = new BigDecimal(abc.countInts(bound));
      }
      else if(model_counting_vars.size() == numStringVar) {
          count = new BigDecimal(abc.countStrs(16));
      }
      else {
        count = new BigDecimal(1);
        if(multiTrackissueFlag) {
          count = new BigDecimal(abc.countVariable(model_counting_vars.get(0).getKey(), bound));
        } else {
          for (Pair<String,String> var : model_counting_vars) {
            if(var.getKey().equals("java.lang.Character"))
              continue;
            count = count.multiply(new BigDecimal(abc.countVariable(var.getKey(), bound)));
          }
        }
      }

      endTime = System.nanoTime();
      System.out.println("Model counting time: " + (endTime - startTime) / 1000000000.0);
    } else {
      count = BigDecimal.ZERO;
      System.out.println("Unsatisfiable");
    }

    return count;
  }

  public void disposeABC() {
    this.abc.dispose();
  }

  public static void main(String[] args) {

    ModelCounter mc = new ModelCounter(4, "abc.string");

    String constraint = "(declare-fun h () String)\n" +
            "(declare-fun l () String)\n" +
            "(assert (in h /[A-Z]{0,4}/))\n" +
            "(assert (in l /[A-Z]{0,4}/))\n" +
            "\n" +
            "(assert (not (= (len  l) (len  h))))\n" +
            "(assert (<= (len  l) 4))\n" +
            "(assert (<= (len  h) 4))\n" +
            "(check-sat)";

    List<Pair<String,String>> model_counting_vars = new ArrayList<>();
    model_counting_vars.add(new Pair<String,String>("l","java.lang.String"));
    model_counting_vars.add(new Pair<String,String>("h","java.lang.String"));
    BigDecimal count = mc.getModelCount(constraint, model_counting_vars, false);

    System.out.println(count);

    mc.disposeABC();
  }

}