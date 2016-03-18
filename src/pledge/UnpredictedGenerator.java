/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package pledge;

/**
 *
 * @author japarejo
 */
public class UnpredictedGenerator {
    public static void main(String[] args){
    String [] args2={"generate_products","-fm",
        "/home/japarejo/workspace/papers/ManyObjectiveSPLTesting/data/exploratoryExperiment/models/realistic/ZipMe.xml"
        ,"-o",
        "/home/japarejo/workspace/papers/ManyObjectiveSPLTesting/data/exploratoryExperiment/models/realistic/Products-ZipMe.csv",
        "-nbProds",
        "10"
    };
    Main.main(args2);
    }
    
}
