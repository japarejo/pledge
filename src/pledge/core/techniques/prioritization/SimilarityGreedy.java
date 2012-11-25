/*
 * Author : Christopher Henard (christopher.henard@uni.lu)
 * Date : 01/11/2012
 * Copyright 2012 University of Luxembourg – Interdisciplinary Centre for Security Reliability and Trust (SnT)
 * All rights reserved
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.

 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.

 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */
package pledge.core.techniques.prioritization;

import java.util.ArrayList;
import java.util.List;
import pledge.core.ModelPLEDGE;
import pledge.core.Product;
import pledge.core.techniques.DistancesUtil;

/**
 *
 * @author Christopher Henard
 */
public class SimilarityGreedy implements PrioritizationTechnique {

    public static final String NAME = "Similarity / Greedy";
    private double fitnessSum;

    @Override
    public List<Product> prioritize(ModelPLEDGE model, List<Product> products) throws Exception {
        int size = products.size();
        List<Product> prioritizedProducts = new ArrayList<Product>(size);
        List<Product> productsCopy = new ArrayList<Product>(products);
        double[][] distancesMatrix = new double[size][size];
        fitnessSum = 0;

        //model.setCurrentAction("Computing the distances...");
        // Computation of the distances
        
        double total = products.size() * (products.size() -1)/2;
        double done = 0;
        
        for (int i = 0; i < distancesMatrix.length; i++) {
            for (int j = 0; j < distancesMatrix.length; j++) {
                distancesMatrix[i][j] = -1;
                if (j > i) {

                    double dist = DistancesUtil.getJaccardDistance(productsCopy.get(i), productsCopy.get(j));
                    distancesMatrix[i][j] = dist;
                    fitnessSum += dist;
                    done++;
                    //model.setProgress((int) (done/total * 100.0));
                }

            }

        }
        //model.setCurrentAction("Ordering the products...");
        //model.setProgress(0);
        // Selection
        while (!productsCopy.isEmpty()) {
            
            if (productsCopy.size() != 1) {
                double dmax = -1;
                int toAddIIndex = -1;
                int toAddJIndex = -1;
                for (int i = 0; i < distancesMatrix.length; i++) {
                    for (int j = 0; j < distancesMatrix.length; j++) {
                        if (j > i) {
                            if (distancesMatrix[i][j] > dmax) {
                                dmax = distancesMatrix[i][j];
                                toAddIIndex = i;
                                toAddJIndex = j;
                            }
                        }
                    }
                }

                Product pi = products.get(toAddIIndex);
                Product pj = products.get(toAddJIndex);
                prioritizedProducts.add(pi);
                prioritizedProducts.add(pj);
                productsCopy.remove(pi);
                productsCopy.remove(pj);

                for (int i = 0; i < distancesMatrix.length; i++) {
                    distancesMatrix[toAddIIndex][i] = distancesMatrix[i][toAddIIndex] = distancesMatrix[i][toAddJIndex] = distancesMatrix[toAddJIndex][i] = -1;
                }
            } else {
                prioritizedProducts.add(productsCopy.get(0));
                productsCopy.clear();
            }
            //model.setProgress((int) ((double) prioritizedProducts.size()/products.size() * 100.0));
        }

        return prioritizedProducts;
    }

    @Override
    public String getName() {
        return NAME;
    }

    @Override
    public double getFitnessSum() {
        return fitnessSum;
    }
}
