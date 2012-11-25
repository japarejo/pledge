package pledge.core;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Observable;
import java.util.StringTokenizer;
import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.minisat.core.IOrder;
import org.sat4j.minisat.core.Solver;
import org.sat4j.minisat.orders.RandomLiteralSelectionStrategy;
import org.sat4j.minisat.orders.RandomWalkDecorator;
import org.sat4j.minisat.orders.VarOrderHeap;
import org.sat4j.reader.DimacsReader;
import org.sat4j.specs.IConstr;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.TimeoutException;
import org.sat4j.tools.ModelIterator;
import pledge.core.techniques.generation.EvolutionaryAlgorithm1Plus1;
import pledge.core.techniques.generation.GenerationTechnique;
import pledge.core.techniques.generation.Individual;
import pledge.core.techniques.prioritization.PrioritizationTechnique;
import pledge.core.techniques.prioritization.SimilarityGreedy;
import pledge.core.techniques.prioritization.SimilarityNearOptimal;
import splar.core.fm.FeatureModel;
import splar.core.fm.XMLFeatureModel;
import splar.plugins.reasoners.sat.sat4j.FMReasoningWithSAT;
import splar.plugins.reasoners.sat.sat4j.ReasoningWithSAT;

/**
 *
 * @author Christopher Henard
 */
public class ModelPLEDGE extends Observable {

    private static final int SAT_TIMEOUT = 1000;
    private static final int ITERATOR_TIMEOUT = 150000;
    private static final String solverName = "MiniSAT";
    public static final String OR = "   OR    ";
    public static final String NOT = "! ";
    private static final IOrder order = new RandomWalkDecorator(new VarOrderHeap(new RandomLiteralSelectionStrategy()), 1);
    private static final String GLOBAL_ACTION_LOAD_FM = "Loading the Feature Model";
    private static final String GLOBAL_ACTION_LOAD_PRODUCTS = "Loading Products";
    private static final String GLOBAL_ACTION_GENERATING_PRODUCTS = "Generating products";
    private static final String GLOBAL_ACTION_PRIORITIZING_PRODUCTS = "Prioritizing products";
    private static final String CURRENT_ACTION_LOAD_CONSTRAINTS = "Loading the constraints...";
    private static final String CURRENT_ACTION_EXTRACT_FEATURES = "Extracting the features...";
    private static final String CURRENT_ACTION_EXTRACT_CONSTRAINTS = "Extracting the constraints...";
    private static final String CURRENT_ACTION_FINDING_CORE_DEAD_FEATURES = "Finding core and dead features...";
    private static final String CORE_FEATURE = "Core";
    private static final String DEAD_FEATURE = "Dead";
    private static final String FREE_FEATURE = "Free";

    public static enum FeatureModelFormat {

        SPLOT, DIMACS
    };
    private Solver solver;
    private ISolver solverIterator;
    private List<Integer> featuresIntList;
    private List<String> featuresList;
    private Map<String, Integer> namesToFeaturesInt;
    private List<IConstr> featureModelConstraints;
    private List<String> featureModelConstraintsString;
    private FeatureModelFormat featureModelFormat;
    private String featureModelName;
    private boolean running, indeterminate;
    private String globalAction, currentAction;
    private List<String> coreFeatures, deadFeatures;
    private int progress;
    private List<Product> products;
    private List<GenerationTechnique> generationTechniques;
    private GenerationTechnique generationTechnique;
    private List<PrioritizationTechnique> prioritizationTechniques;
    private PrioritizationTechnique prioritizationTechnique;
    private long generationTimeMSAllowed = 60000;
    private int nbProductsToGenerate = 10;
    private String fmPath;

    public ModelPLEDGE() {
        solver = null;
        solverIterator = null;
        featuresIntList = new ArrayList<Integer>();
        featuresList = new ArrayList<String>();
        namesToFeaturesInt = new HashMap<String, Integer>();
        featureModelConstraints = new ArrayList<IConstr>();
        featureModelConstraintsString = new ArrayList<String>();
        coreFeatures = new ArrayList<String>();
        deadFeatures = new ArrayList<String>();
        products = null;
        running = false;
        indeterminate = true;
        progress = 0;
        generationTechniques = new ArrayList<GenerationTechnique>();
        generationTechniques.add(new EvolutionaryAlgorithm1Plus1());
        generationTechnique = generationTechniques.get(0);
        prioritizationTechniques = new ArrayList<PrioritizationTechnique>();
        prioritizationTechniques.add(new SimilarityGreedy());
        prioritizationTechniques.add(new SimilarityNearOptimal());
        prioritizationTechnique = prioritizationTechniques.get(0);
    }

    public FeatureModelFormat getFeatureModelFormat() {
        return featureModelFormat;
    }

    public String getFeatureModelName() {
        return featureModelName;
    }

    public List<Integer> getFeaturesIntList() {
        return featuresIntList;
    }

    public List<String> getFeaturesList() {
        return featuresList;
    }

    public Map<String, Integer> getNamesToFeaturesInt() {
        return namesToFeaturesInt;
    }

    public List<IConstr> getFeatureModelConstraints() {
        return featureModelConstraints;
    }

    public List<String> getFeatureModelConstraintsString() {
        return featureModelConstraintsString;
    }

    public Solver getSolver() {
        return solver;
    }

    public boolean isRunning() {
        return running;
    }

    public List<Product> getProducts() {
        return products;
    }

    public long getGenerationTimeMSAllowed() {
        return generationTimeMSAllowed;
    }

    public void setGenerationTimeMSAllowed(long generationTimeMSAllowed) {
        this.generationTimeMSAllowed = generationTimeMSAllowed;
        setChanged();
        notifyObservers();
    }

    public int getNbProductsToGenerate() {
        return nbProductsToGenerate;
    }

    public void setNbProductsToGenerate(int nbProductsToGenerate) {
        this.nbProductsToGenerate = nbProductsToGenerate;
        setChanged();
        notifyObservers();
    }

    public void setRunning(boolean running) {
        this.running = running;
        if (!running) {
            indeterminate = true;
        }
        progress = 0;
        setChanged();
        notifyObservers();
    }

    public boolean isIndeterminate() {
        return indeterminate;
    }

    public int getProgress() {
        return progress;
    }

    public void setProgress(int progress) {
        this.progress = progress;
        setChanged();
        notifyObservers();
    }

    public void setIndeterminate(boolean indeterminate) {
        this.indeterminate = indeterminate;
        setChanged();
        notifyObservers();
    }

    public ISolver getSolverIterator() {
        return solverIterator;
    }

    public void setSolverIterator(ISolver solverIterator) {
        this.solverIterator = solverIterator;
    }

    public String getCurrentAction() {
        return currentAction;
    }

    public void setCurrentAction(String currentAction) {
        this.currentAction = currentAction;
        setChanged();
        notifyObservers();
    }

    public String getGlobalAction() {
        return globalAction;
    }

    public void setGlobalAction(String globalAction) {
        this.globalAction = globalAction;
        setChanged();
        notifyObservers();
    }

    private void clean() {
        featuresIntList.clear();
        featuresList.clear();
        namesToFeaturesInt.clear();
        featureModelConstraints.clear();
        featureModelConstraintsString.clear();
        coreFeatures.clear();
        deadFeatures.clear();
        setChanged();
        notifyObservers();
    }

    public List<String> getCoreFeatures() {
        return coreFeatures;
    }

    public List<String> getDeadFeatures() {
        return deadFeatures;
    }

    public GenerationTechnique getGenerationTechnique() {
        return generationTechnique;
    }

    public void SetGenerationTechniqueByName(String name) {
        for (GenerationTechnique gt : generationTechniques) {
            if (gt.getName().equals(name)) {
                generationTechnique = gt;
                break;
            }
        }

    }

    public List<GenerationTechnique> getGenerationTechniques() {
        return generationTechniques;
    }

    public PrioritizationTechnique getPrioritizationTechnique() {
        return prioritizationTechnique;
    }

    public void SetPrioritizationTechniqueByName(String name) {
        for (PrioritizationTechnique pt : prioritizationTechniques) {
            if (pt.getName().equals(name)) {
                prioritizationTechnique = pt;
                break;
            }
        }

    }

    public List<PrioritizationTechnique> getPrioritizationTechniques() {
        return prioritizationTechniques;
    }

    public void loadFeatureModel(String filePath, FeatureModelFormat format) throws Exception {
        setRunning(true);
        setIndeterminate(true);
        setGlobalAction(GLOBAL_ACTION_LOAD_FM);
        setCurrentAction(CURRENT_ACTION_LOAD_CONSTRAINTS);
        featureModelFormat = format;
        clean();
        featureModelName = new File(filePath).getName();
        featureModelName = featureModelName.substring(0, featureModelName.lastIndexOf("."));
        products = null;
        fmPath = filePath;
        switch (format) {

            case SPLOT:
                FeatureModel fm = new XMLFeatureModel(filePath, XMLFeatureModel.USE_VARIABLE_NAME_AS_ID);
                fm.loadModel();
                ReasoningWithSAT reasonerSAT = new FMReasoningWithSAT(solverName, fm, SAT_TIMEOUT);
                reasonerSAT.init();
                solver = (Solver) reasonerSAT.getSolver();
                String[] features = reasonerSAT.getVarIndex2NameMap();
                for (int i = 0; i < features.length; i++) {
                    String featureName = features[i];
                    featuresList.add(featureName);
                    int n = i + 1;
                    featuresIntList.add(n);
                    namesToFeaturesInt.put(featureName, n);
                }

                break;
            case DIMACS:
                ISolver dimacsSolver = SolverFactory.instance().createSolverByName(solverName);
                DimacsReader dr = new DimacsReader(dimacsSolver);
                dr.parseInstance(new FileReader(filePath));
                solver = (Solver) dimacsSolver;
                BufferedReader in = new BufferedReader(new FileReader(filePath));
                String line;
                int n = 0;
                while ((line = in.readLine()) != null && line.startsWith("c")) {
                    StringTokenizer st = new StringTokenizer(line.trim(), " ");
                    st.nextToken();
                    n++;
                    String sFeature = st.nextToken().replace('$', ' ').trim();
                    int feature = Integer.parseInt(sFeature);
                    if (n != feature) {
                        throw new Exception("Incorrect dimacs file, missing feature number " + n + " ?");
                    }
                    String featureName = st.nextToken();
                    featuresIntList.add(feature);
                    featuresList.add(featureName);
                    namesToFeaturesInt.put(featureName, feature);
                }
                in.close();
                break;
        }

        setCurrentAction(CURRENT_ACTION_EXTRACT_FEATURES);
        setIndeterminate(false);
        setProgress(0);
        int n = 1;
        int featuresCount = featuresIntList.size();
        while (n <= featuresCount) {
            featuresIntList.add(-n);
            n++;
            setProgress((int) (n / (double) featuresCount * 100));
        }

        if (solver != null) {
            solver.setTimeout(SAT_TIMEOUT);
        }


        solver.setOrder(order);
        solverIterator = new ModelIterator(solver);
        solverIterator.setTimeoutMs(ITERATOR_TIMEOUT);


        setCurrentAction(CURRENT_ACTION_EXTRACT_CONSTRAINTS);
        setProgress(0);
        int nConstraints = solver.nConstraints();
        for (int i = 0; i < nConstraints; i++) {
            IConstr constraint = solver.getIthConstr(i);
            if (constraint != null) {
                featureModelConstraints.add(constraint);
                StringBuilder stringConstraint = new StringBuilder();
                int size = constraint.size();
                for (int j = 0; j < size; j++) {
                    boolean negative;
                    int literal = constraint.get(j) / 2;
                    negative = constraint.get(j) % 2 == 1;
                    String feature = featuresList.get(literal - 1);
                    if (negative) {
                        stringConstraint.append(NOT);
                    }
                    stringConstraint.append(feature);
                    if (j < size - 1) {
                        stringConstraint.append(OR);
                    }

                }
                featureModelConstraintsString.add(stringConstraint.toString());
            }

            setProgress((int) ((i + 1) / (double) nConstraints * 100));
        }

        setCurrentAction(CURRENT_ACTION_FINDING_CORE_DEAD_FEATURES);
        setProgress(0);
        n = 0;
        IVecInt vector = new VecInt();
        // Core and dead features
        for (String feature : featuresList) {
            int f = namesToFeaturesInt.get(feature);
            vector.clear();
            vector.push(-f);
            if (!solver.isSatisfiable(vector)) {
                coreFeatures.add(feature);
            }

            vector.clear();
            vector.push(f);
            if (!solver.isSatisfiable(vector)) {
                deadFeatures.add(feature);
            }
            n++;
            setProgress((int) ((n) / (double) featuresCount * 100));
        }


        setRunning(false);
        setChanged();
        notifyObservers(featureModelConstraints);
    }

    public void generateProducts() throws Exception {
        setRunning(true);
        setIndeterminate(false);
        setGlobalAction(GLOBAL_ACTION_GENERATING_PRODUCTS);
        products = generationTechnique.generateProducts(this, nbProductsToGenerate, generationTimeMSAllowed, prioritizationTechnique);
        setRunning(false);
        setChanged();
        notifyObservers();
    }

    public void prioritizeProducts() throws Exception {
        setRunning(true);
        setIndeterminate(false);
        setGlobalAction(GLOBAL_ACTION_PRIORITIZING_PRODUCTS);
        products = prioritizationTechnique.prioritize(this, products);
        setRunning(false);
        setChanged();
        notifyObservers();
    }

    public String getFeatureType(String feature) {
        if (coreFeatures.contains(feature)) {
            return CORE_FEATURE;
        } else if (deadFeatures.contains(feature)) {
            return DEAD_FEATURE;
        } else {
            return FREE_FEATURE;
        }
    }

    public Product toProduct(int[] vector) {

        Product product = new Product();
        for (int i : vector) {
            product.add(i);
        }
        return product;
    }

    public List<Product> getUnpredictableProducts(int count) {
        List<Product> products = new ArrayList<Product>(count);

        while (products.size() < count) {

            try {
                if (solverIterator.isSatisfiable()) {
                    Product product = toProduct(solverIterator.model());

                    if (!products.contains(product)) {
                        products.add(product);
                    }

                } else {
                    switch (featureModelFormat) {

                        case SPLOT:
                            FeatureModel fm = new XMLFeatureModel(fmPath, XMLFeatureModel.USE_VARIABLE_NAME_AS_ID);
                            fm.loadModel();
                            ReasoningWithSAT reasonerSAT = new FMReasoningWithSAT(solverName, fm, SAT_TIMEOUT);
                            reasonerSAT.init();
                            solver = (Solver) reasonerSAT.getSolver();
                            break;
                        case DIMACS:
                            ISolver dimacsSolver = SolverFactory.instance().createSolverByName(solverName);
                            DimacsReader dr = new DimacsReader(dimacsSolver);
                            dr.parseInstance(new FileReader(fmPath));
                            solver = (Solver) dimacsSolver;
                            break;
                    }
                    solver.setTimeout(SAT_TIMEOUT);
                    solver.setOrder(order);
                    solverIterator = new ModelIterator(solver);
                    solverIterator.setTimeoutMs(ITERATOR_TIMEOUT);
                }

            } catch (Exception e) {
                e.printStackTrace();
            }
        }
        return products;
    }

    public void saveProducts(String outFile) throws Exception {



            BufferedWriter out = new BufferedWriter(new FileWriter(outFile));

            int featuresCount = featuresList.size();
            for (int i = 1; i <= featuresCount; i++) {
                out.write(i + "->" + this.featuresList.get(i-1));
                    out.newLine();
            }
            for (Product product : products) {
                int done = 0;
                for (Integer feature : product) {
                    out.write(""+feature);
                    if (done < product.size()) {
                        out.write(";");
                    }
                    done++;
                }

                out.newLine();
            }
            out.close();


    }
    
    public void saveProducts2(String outFile) throws Exception {

        String sout = outFile;
        if (! outFile.endsWith("/"))
            sout+="/";
        int j = 1;
        for (Product product : products) {

            BufferedWriter out = new BufferedWriter(new FileWriter(sout + "product_" + j + ".config"));

//            int featuresCount = featuresList.size();
//            for (int i = 1; i <= featuresCount; i++) {
//                out.write(i + "->" + this.featuresList.get(i - 1));
//                out.newLine();
//            }
//            int done = 0;
            for (Integer feature : product) {
                if (feature > 0) {
                    out.write(featuresList.get(feature - 1));
                    out.newLine();
                }

                
            }

            out.close();
            j++;
        }
    }

    public void loadProducts(String inFile) throws Exception {
        setRunning(true);
        setIndeterminate(true);
        setGlobalAction(GLOBAL_ACTION_LOAD_PRODUCTS);
        solver = null;
        solverIterator = null;
        featuresIntList = new ArrayList<Integer>();
        featuresList = new ArrayList<String>();
        namesToFeaturesInt = new HashMap<String, Integer>();
        featureModelConstraints = new ArrayList<IConstr>();
        featureModelConstraintsString = new ArrayList<String>();
        coreFeatures = new ArrayList<String>();
        deadFeatures = new ArrayList<String>();
        BufferedReader in = new BufferedReader(new FileReader(inFile));

        products = new ArrayList<Product>();
        String line;

        while ((line = in.readLine()) != null) {
            if (!line.contains(">")) {
                Product p = new Product();
                setCurrentAction("Extracting product number" + products.size());
                StringTokenizer st = new StringTokenizer(line, ";");
                while (st.hasMoreTokens()) {
                    p.add(Integer.parseInt(st.nextToken()));
                }
                products.add(p);
            }
            else{
                featuresList.add(line.substring(line.indexOf(">")+1, line.length()));
            }
        }
        setRunning(false);
        setChanged();
        notifyObservers(this);
    }

    public void quit() {
        System.exit(0);
    }
}
