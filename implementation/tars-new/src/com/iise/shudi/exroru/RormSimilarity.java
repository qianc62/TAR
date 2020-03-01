package com.iise.shudi.exroru;

import org.jbpt.petri.NetSystem;
import org.jbpt.petri.Transition;
import org.jbpt.petri.io.PNMLSerializer;
import org.jbpt.petri.unfolding.Event;
import org.jbpt.petri.unfolding.OrderingRelationType;
import org.jbpt.petri.unfolding.ProperCompletePrefixUnfolding;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

/**
 * @author Wang Shuhao
 */
public class RormSimilarity {

    public static void main(String[] args) throws Exception {
        // String filePath = "/Users/shudi/Desktop/multi_relation_1.pnml";
        // String filePath =
        // "/Users/shudi/Desktop/parallel_A_with_outer_loop.pnml";
        // String filePath = "/Users/shudi/Desktop/M15.pnml";

//        PNMLSerializer pnmlSerializer = new PNMLSerializer();
//        String filePath =
//                "C:\\Users\\Shudi\\Desktop\\rorm\\test\\parallel_inv_1_a.pnml";
//        NetSystem net = pnmlSerializer.parse(filePath);
//        RefinedOrderingRelationsMatrix rorm = new
//                RefinedOrderingRelationsMatrix((NetSystem) net.clone());
//        rorm.printMatrix();
//        rorm.print();

        PNMLSerializer pnmlSerializer = new PNMLSerializer();
        RefinedOrderingRelation.SDA_WEIGHT = 0.0;
        RefinedOrderingRelation.IMPORTANCE = true;
        String filepath1 = "C:\\Users\\Shudi\\Desktop\\rorm\\test\\M0.pnml";
        String filepath2 = "C:\\Users\\Shudi\\Desktop\\rorm\\test\\M0.pnml";
        NetSystem net1 = pnmlSerializer.parse(filepath1);
        NetSystem net2 = pnmlSerializer.parse(filepath2);
        RormSimilarity rorm = new RormSimilarity();
        float sim = rorm.similarity(net1, net2);
//        BehavioralProfileSimilarity bp = new BehavioralProfileSimilarity();
//        float sim = bp.similarity(net1, net2);
        if (sim == Float.MIN_VALUE) {
            System.out.println("Invalid Net System");
        } else {
            System.out.println(sim);
        }
    }

    public float similarity(NetSystem net1, NetSystem net2) {
        RefinedOrderingRelationsMatrix rorm1 = new RefinedOrderingRelationsMatrix((NetSystem) net1.clone());
        RefinedOrderingRelationsMatrix rorm2 = new RefinedOrderingRelationsMatrix((NetSystem) net2.clone());
        if (!rorm1.isValid() || !rorm2.isValid()) {
            return Float.MIN_VALUE;
        }
        return similarityWithNever(rorm1, rorm2);
    }

    private void outputPureTARS(ProperCompletePrefixUnfolding cpu, boolean outputOn)
    {
    	Hashtable<String, Set<String>> tars = cpu.getPureTARs(); 
    	Iterator<String> iter = tars.keySet().iterator();
    	System.out.println("------Pure TAR----------");
    	while (iter.hasNext())
    	{
    		String t1 = iter.next();
    		Set<String> t2s = tars.get(t1);
    		for (String t2 : t2s)
    		{
    			System.out.println(t1 + "-->" + t2);
    		}
    	}
    	
    	tars = cpu.getPureTAR_Accelerated();
    	iter = tars.keySet().iterator();
    	System.out.println("------Pure TAR Accelerated----------");
    	while (iter.hasNext())
    	{
    		String t1 = iter.next();
    		Set<String> t2s = tars.get(t1);
    		for (String t2 : t2s)
    		{
    			System.out.println(t1 + "-->" + t2);
    		}
    	}
    }
    
    // added by jisheng to print out the TARs calculated using CPU
    private void outputTARs(ProperCompletePrefixUnfolding cpu, boolean outputOn) throws Exception
    {
		Set<Event> events = cpu.getEvents();
		Hashtable<String,Set<String>> transitionTAR = new Hashtable<String,Set<String>>();
		for (Event e : events)
		{
			for (Event anotherE : events)
				if (cpu.isSequentialTar(e, anotherE)) 
				{
					if (e.getTransition().getLabel().length() == 0) continue;
					if (anotherE.getTransition().getLabel().length() == 0) continue;
					
					if (transitionTAR.get(e.getTransition().getLabel()) == null) transitionTAR.put(e.getTransition().getLabel(), new HashSet<String>());
					transitionTAR.get(e.getTransition().getLabel()).add(anotherE.getTransition().getLabel());
					//System.out.println("" + e.getTransition().getLabel() + "-->" + anotherE.getTransition().getLabel());
				}
			//System.out.println();
		}
		
		if (outputOn) {
			for (String foo : transitionTAR.keySet()) {
				for (String bar : transitionTAR.get(foo))
				{
					if (foo.length() * bar.length() == 0) continue;
					System.out.println(foo + "-->" + bar);
				}
			}
		
		}
    }
    
    // added by jisheng to test the consistency of TAR calculation
    private boolean consistencyCheck(NetSystem net, RefinedOrderingRelationsMatrix rorm)
    {
    	int i, j;
    	int dimension = rorm.getConcurrentMatrix().length;
		ProperCompletePrefixUnfolding cpu = rorm.getCPU();
		List<String> tName = rorm.gettName();
		
		List<Transition> alObTransitions = new ArrayList<>(net.getObservableTransitions());
		RefinedOrderingRelation[][] concurrencyMatrix = rorm.getConcurrentMatrix();
		RefinedOrderingRelation[][] causalMatrix = rorm.getCausalMatrix();
				
		boolean[][] coveredMatrix = new boolean[concurrencyMatrix.length][concurrencyMatrix.length];
		boolean[][] markedMatrix = new boolean[concurrencyMatrix.length][concurrencyMatrix.length];
		boolean[][] tarMatrix = new boolean[concurrencyMatrix.length][concurrencyMatrix.length];
		boolean[][] tarMarkedMatrix = new boolean[concurrencyMatrix.length][concurrencyMatrix.length];
		
		for (i = 0; i < concurrencyMatrix.length; i++)
		{
			for (j = 0; j < concurrencyMatrix.length; j++)
			{
			    RefinedOrderingRelation rel = concurrencyMatrix[i][j];
	            boolean isConcurrent = !(rel.getRelation() == Relation.NEVER);
	            coveredMatrix[i][j] = isConcurrent;
	            markedMatrix[i][j] = isConcurrent;
	            
	            if (causalMatrix[i][j].getRelation() != Relation.NEVER && causalMatrix[i][j].isAdjacency())
	            {
	            	tarMatrix[i][j] = true;
	            	tarMarkedMatrix[i][j] = true;
	            }
	            else 
	            {
	            	tarMatrix[i][j] = false;
	            	tarMarkedMatrix[i][j] = false;
	            }
			}
		}
		
		Set<Event> events = cpu.getEvents();
		for (Event e : events)
		{
			for (Event anotherE : events)
			{
				if (anotherE == e) continue;

				/*
				//System.out.println(cpu.getOrderingRelation(e, anotherE));
				if (cpu.getOrderingRelation(e, anotherE) == OrderingRelationType.CONCURRENT)
				{
					int targetX = tName.indexOf(e.getPetriNetNode().getLabel());
					int targetY = tName.indexOf(anotherE.getPetriNetNode().getLabel());
					
		            RefinedOrderingRelation rel = concurrencyMatrix[targetX][targetY];
		            
		            boolean isConcurrent = !(rel.getRelation() == Relation.NEVER);
					markedMatrix[targetX][targetY] = false;
					
					System.out.println(e.getPetriNetNode().getLabel());
					System.out.println(anotherE.getPetriNetNode().getLabel());
					
					System.out.println("!");
					if (isConcurrent) System.out.println("Consistent!");
					else System.out.println("Inconsistent!");
				}
				*/

				if (cpu.isSequentialTar(e, anotherE))
				{
					//int targetX = rorm.mapEventToIndex(e);
					//int targetY = rorm.mapEventToIndex(anotherE);
					int targetX = tName.indexOf(e.getPetriNetNode().getLabel());
					int targetY = tName.indexOf(anotherE.getPetriNetNode().getLabel());
					
		            RefinedOrderingRelation rel = causalMatrix[targetX][targetY];

					tarMarkedMatrix[targetX][targetY] = false;

		            boolean isTar = !(rel.getRelation() == Relation.NEVER) && rel.isAdjacency();
					
					System.out.println(e.getPetriNetNode().getLabel());
					System.out.println(anotherE.getPetriNetNode().getLabel());
					
					System.out.println("!");
					if (isTar) System.out.println("TAR Consistent!");
					else System.out.println("TAR Inconsistent!");

				}

			}
		}
		
		
		for (i = 0; i < concurrencyMatrix.length; i++)
		{
			for (j = 0; j < concurrencyMatrix.length; j++)
			{
				/*
				if (markedMatrix[i][j] == true)
				{
					System.out.println("Not Covered!");
				}
				*/
				if (tarMarkedMatrix[i][j] == true)
				{
					System.out.println("TAR not Covered!");
				}

			}
		}
		
		/*
		List<String> tName = rorm.gettName();
		for (i = 0; i < alObTransitions.size(); i++) {
	            Transition fromTransition = alObTransitions.get(i);

	    		for (j = i + 1; j < alObTransitions.size(); j++) {
		            Transition toTransition = alObTransitions.get(j);
		            
		            RefinedOrderingRelation rel = concurrencyMatrix[tName.indexOf(fromTransition.getLabel())][tName
                                                                                   .indexOf(toTransition.getLabel())];
		            boolean isConcurrent = !(rel.getRelation() == Relation.NEVER);

		            
		            Set<Transition> transitions = cpu.getOccurrenceNet().getTransitions();
		            ArrayList<Transition> fromTransitions = new ArrayList<Transition>();
		            ArrayList<Transition> toTransitions = new ArrayList<Transition>();
		            
		            Iterator<Transition> iter = transitions.iterator();
		            while(iter.hasNext())
		            {
		            	Transition current = iter.next();
		            	String str = current.getLabel().split("-")[0];
		            	if (str.compareTo(toTransition.getLabel()) == 0)
		            	{
		            		toTransitions.add(current);
		            	}
		            	if (str.compareTo(fromTransition.getLabel())== 0)
		            	{
		            		fromTransitions.add(current);
		            	}
		            }
		            
		            boolean flag = false;
		            for (Transition f : fromTransitions)
		            {
		            	for (Transition t : toTransitions)
		            	{
		            		if (cpu.areConcurrent(cpu.getOccurrenceNet().getUnfoldingNode(f), cpu.getOccurrenceNet().getUnfoldingNode(t))){
		            			flag = true;
		            			break;
		            		}
		            		//cpu.get
		            	}
		            }
		            
		            if (flag == isConcurrent) System.out.println("Yes!");
		            
	    		}

		}
		*/
    	return true;
    }
    
    
    /*
     * added by jisheng
     * 08/11/15
     */
    public long[] rormTest(NetSystem net1, NetSystem net2, boolean outputTAROn) throws Exception
    {
    	long[] times = new long[4];
    	RefinedOrderingRelationsMatrix rorm1 = new RefinedOrderingRelationsMatrix((NetSystem) net1.clone());
    	/*
    	for (int i = 0; i < rorm1.gettName().size(); i++)
    	{
    		System.out.print(rorm1.gettName().get(i) + "| ");
        	for (int j = 0; j < rorm1.gettName().size(); j++) {
        		System.out.print(rorm1.gettName().get(j) + ": " + rorm1.getCausalMatrix()[i][j] + " ");
        	}
        	System.out.println();
    	}
    	 */
        //RefinedOrderingRelationsMatrix rorm2 = new RefinedOrderingRelationsMatrix((NetSystem) net2.clone());

    	if (rorm1.getCPU() == null) return times;
    	
    	long start = System.nanoTime();
    	//outputTARs(rorm1.getCPU(),outputTAROn);
    	long aggregateTime = System.nanoTime() - start;
    	
    	rorm1.getCPU().makePureTAR();  	
    	rorm1.getCPU().makePureTAR();
    	long pureAcceleratedTime = rorm1.getCPU().makePureTAR_Accelerated();
    	pureAcceleratedTime = rorm1.getCPU().makePureTAR_Accelerated();
    	//this.outputPureTARS(rorm1.getCPU(), outputTAROn);
    	if (outputTAROn) {
    		Hashtable<String,Set<String>> tars = rorm1.getCPU().getPureTAR_Accelerated();
    		for (String key : tars.keySet())
    		{
    			Set<String> succSet = tars.get(key);
    			for (String succ : succSet)  
    				System.out.println("TAR: " + key + "->" + succ);
    			
    		}
    	}
        times[0] = rorm1.getCPUTime(); //+ rorm2.getCPUTime();
       
        times[1] = rorm1.getTARTime() + aggregateTime; //+ rorm2.getTARTime();
        // note that getTARTime() is DEPRECATED since it uses an old and deprecated implementation.
        
        times[2] = rorm1.getCPU().getPureTARTime(); // GENERAL
        times[3] = pureAcceleratedTime;				// IMPROVED

        return times;
    }
    
    public long[] similarityWithTime(NetSystem net1, NetSystem net2) {
        RefinedOrderingRelationsMatrix rorm1 = new RefinedOrderingRelationsMatrix((NetSystem) net1.clone());
        RefinedOrderingRelationsMatrix rorm2 = new RefinedOrderingRelationsMatrix((NetSystem) net2.clone());
        
        
        //ProperCompletePrefixUnfolding cpu = rorm1.getCPU();

        //consistencyCheck(net1, rorm1);

        
        if (!rorm1.isValid() || !rorm2.isValid()) {
            return null;
        }
        long start = System.currentTimeMillis();
        
        // pjs commented out
        //similarityWithNever(rorm1, rorm2);
        long simTime = System.currentTimeMillis() - start;
        long[] times = new long[2 + rorm1.getComputationTime().length + rorm2.getComputationTime().length];
        
        int i = 1;
        long totalTime = 0;
        for (long l : rorm1.getComputationTime()) {
            times[i++] = l;
            totalTime += l;
        }
        for (long l : rorm2.getComputationTime()) {
            times[i++] = l;
            totalTime += l;
        }
        times[i++] = simTime;
        totalTime += simTime;
        times[0] = totalTime;
        return times;
    }

    public float similarityWithoutNever(RefinedOrderingRelationsMatrix matrix1, RefinedOrderingRelationsMatrix matrix2) {
        List<String> tName1 = matrix1.gettName();
        List<String> tName2 = matrix2.gettName();
        Set<String> interNames = new HashSet<>();
        interNames.addAll(tName1);
        interNames.retainAll(tName2);
        /* intersectionWithoutNever */
        double causalInter = 0.0, inverseCausalInter = 0.0, concurrentInter = 0.0;
        for (String si : interNames) {
            int idx1i = tName1.indexOf(si);
            int idx2i = tName2.indexOf(si);
            for (String sj : interNames) {
                int idx1j = tName1.indexOf(sj);
                int idx2j = tName2.indexOf(sj);
                causalInter += matrix1.getCausalMatrix()[idx1i][idx1j]
                        .intersectionWithoutNever(matrix2.getCausalMatrix()[idx2i][idx2j]);
                inverseCausalInter += matrix1.getInverseCausalMatrix()[idx1i][idx1j]
                        .intersectionWithoutNever(matrix2.getInverseCausalMatrix()[idx2i][idx2j]);
                concurrentInter += matrix1.getConcurrentMatrix()[idx1i][idx1j]
                        .intersectionWithoutNever(matrix2.getConcurrentMatrix()[idx2i][idx2j]);
            }
        }
        /* unionWithoutNever */
        double causalUnion = 0.0, inverseCausalUnion = 0.0, concurrentUnion = 0.0;
        int causalUnionSize = 0, inverseCausalUnionSize = 0, concurrentUnionSize = 0;
        for (int i = 0; i < tName1.size(); ++i) {
            int idx2i = tName2.indexOf(tName1.get(i));
            for (int j = 0; j < tName1.size(); ++j) {
                int idx2j = tName2.indexOf(tName1.get(j));
                if (idx2i != -1 && idx2j != -1) {
                    causalUnion += matrix1.getCausalMatrix()[i][j].unionWithoutNever(matrix2.getCausalMatrix()[idx2i][idx2j]);
                    inverseCausalUnion += matrix1.getInverseCausalMatrix()[i][j]
                            .unionWithoutNever(matrix2.getInverseCausalMatrix()[idx2i][idx2j]);
                    concurrentUnion += matrix1.getConcurrentMatrix()[i][j]
                            .unionWithoutNever(matrix2.getConcurrentMatrix()[idx2i][idx2j]);
                    if (matrix1.getCausalMatrix()[i][j].getRelation() != Relation.NEVER
                            || matrix2.getCausalMatrix()[idx2i][idx2j].getRelation() != Relation.NEVER) {
                        ++causalUnionSize;
                    }
                    if (matrix1.getInverseCausalMatrix()[i][j].getRelation() != Relation.NEVER
                            || matrix2.getInverseCausalMatrix()[idx2i][idx2j].getRelation() != Relation.NEVER) {
                        ++inverseCausalUnionSize;
                    }
                    if (matrix1.getConcurrentMatrix()[i][j].getRelation() != Relation.NEVER
                            || matrix2.getConcurrentMatrix()[idx2i][idx2j].getRelation() != Relation.NEVER) {
                        ++concurrentUnionSize;
                    }
                } else {
                    causalUnion += matrix1.getCausalMatrix()[i][j].getRelation() == Relation.NEVER ? 0
                            : matrix1.getCausalMatrix()[i][j].getImportance();
                    inverseCausalUnion += matrix1.getInverseCausalMatrix()[i][j].getRelation() == Relation.NEVER ? 0
                            : matrix1.getInverseCausalMatrix()[i][j].getImportance();
                    concurrentUnion += matrix1.getConcurrentMatrix()[i][j].getRelation() == Relation.NEVER ? 0
                            : matrix1.getConcurrentMatrix()[i][j].getImportance();
                    causalUnionSize += matrix1.getCausalMatrix()[i][j].getRelation() == Relation.NEVER ? 0 : 1;
                    inverseCausalUnionSize += matrix1.getInverseCausalMatrix()[i][j].getRelation() == Relation.NEVER ? 0 : 1;
                    concurrentUnionSize += matrix1.getConcurrentMatrix()[i][j].getRelation() == Relation.NEVER ? 0 : 1;
                }
            }
        }
        for (int i = 0; i < tName2.size(); ++i) {
            int idx1i = tName1.indexOf(tName2.get(i));
            for (int j = 0; j < tName2.size(); ++j) {
                int idx1j = tName1.indexOf(tName2.get(j));
                if (idx1i == -1 || idx1j == -1) {
                    causalUnion += matrix2.getCausalMatrix()[i][j].getRelation() == Relation.NEVER ? 0
                            : matrix2.getCausalMatrix()[i][j].getImportance();
                    inverseCausalUnion += matrix2.getInverseCausalMatrix()[i][j].getRelation() == Relation.NEVER ? 0
                            : matrix2.getInverseCausalMatrix()[i][j].getImportance();
                    concurrentUnion += matrix2.getConcurrentMatrix()[i][j].getRelation() == Relation.NEVER ? 0
                            : matrix2.getConcurrentMatrix()[i][j].getImportance();
                    causalUnionSize += matrix2.getCausalMatrix()[i][j].getRelation() == Relation.NEVER ? 0 : 1;
                    inverseCausalUnionSize += matrix2.getInverseCausalMatrix()[i][j].getRelation() == Relation.NEVER ? 0 : 1;
                    concurrentUnionSize += matrix2.getConcurrentMatrix()[i][j].getRelation() == Relation.NEVER ? 0 : 1;
                }
            }
        }
        // Jaccard
        double causalSim = causalUnion == 0 ? 0 : causalInter / causalUnion;
        double inverseCausalSim = inverseCausalUnion == 0 ? 0 : inverseCausalInter / inverseCausalUnion;
        double concurrentSim = concurrentUnion == 0 ? 0 : concurrentInter / concurrentUnion;
        int unionSize = causalUnionSize + inverseCausalUnionSize + concurrentUnionSize;
        double causalWeight = ((double) causalUnionSize) / ((double) unionSize);
        double inverseCausalWeight = ((double) inverseCausalUnionSize) / ((double) unionSize);
        double concurrentWeight = ((double) concurrentUnionSize) / ((double) unionSize);
        System.out.println(causalSim + " " + inverseCausalSim + " " + concurrentSim);
        return (float) (causalSim * causalWeight + inverseCausalSim * inverseCausalWeight
                + concurrentSim * concurrentWeight);
    }

    public float similarityWithNever(RefinedOrderingRelationsMatrix matrix1, RefinedOrderingRelationsMatrix matrix2) {
        List<String> tName1 = matrix1.gettName();
        List<String> tName2 = matrix2.gettName();
        /* intersectionWithNever */
        Set<String> interNames = new HashSet<>();
        interNames.addAll(tName1);
        interNames.retainAll(tName2);
        double causalInter = 0.0, inverseCausalInter = 0.0, concurrentInter = 0.0;
        for (String si : interNames) {
            int idx1i = tName1.indexOf(si);
            int idx2i = tName2.indexOf(si);
            for (String sj : interNames) {
                int idx1j = tName1.indexOf(sj);
                int idx2j = tName2.indexOf(sj);
                causalInter += matrix1.getCausalMatrix()[idx1i][idx1j]
                        .intersectionWithNever(matrix2.getCausalMatrix()[idx2i][idx2j]);
                inverseCausalInter += matrix1.getInverseCausalMatrix()[idx1i][idx1j]
                        .intersectionWithNever(matrix2.getInverseCausalMatrix()[idx2i][idx2j]);
                concurrentInter += matrix1.getConcurrentMatrix()[idx1i][idx1j]
                        .intersectionWithNever(matrix2.getConcurrentMatrix()[idx2i][idx2j]);
            }
        }
        /* unionWithNever */
        Set<String> unionNames = new HashSet<>();
        unionNames.addAll(tName1);
        unionNames.addAll(tName2);
        double causalUnion = 0.0, inverseCausalUnion = 0.0, concurrentUnion = 0.0;
        for (String si : unionNames) {
            int idx1i = tName1.indexOf(si);
            int idx2i = tName2.indexOf(si);
            for (String sj : unionNames) {
                int idx1j = tName1.indexOf(sj);
                int idx2j = tName2.indexOf(sj);
                if (idx1i != -1 && idx2i != -1 && idx1j != -1 && idx2j != -1) {
                    causalUnion += matrix1.getCausalMatrix()[idx1i][idx1j].unionWithNever(matrix2.getCausalMatrix()[idx2i][idx2j]);
                    inverseCausalUnion += matrix1.getInverseCausalMatrix()[idx1i][idx1j].unionWithNever(matrix2.getInverseCausalMatrix()[idx2i][idx2j]);
                    concurrentUnion += matrix1.getConcurrentMatrix()[idx1i][idx1j].unionWithNever(matrix2.getConcurrentMatrix()[idx2i][idx2j]);
                } else if (idx1i != -1 && idx1j != -1) {
                    causalUnion += matrix1.getCausalMatrix()[idx1i][idx1j].getImportance();
                    inverseCausalUnion += matrix1.getInverseCausalMatrix()[idx1i][idx1j].getImportance();
                    concurrentUnion += matrix1.getConcurrentMatrix()[idx1i][idx1j].getImportance();
                } else if (idx2i != -1 && idx2j != -1) {
                    causalUnion += matrix2.getCausalMatrix()[idx2i][idx2j].getImportance();
                    inverseCausalUnion += matrix2.getInverseCausalMatrix()[idx2i][idx2j].getImportance();
                    concurrentUnion += matrix2.getConcurrentMatrix()[idx2i][idx2j].getImportance();
                }
            }
        }
        // Jaccard
        double causalSim = causalUnion == 0 ? 0 : causalInter / causalUnion;
        double inverseCausalSim = inverseCausalUnion == 0 ? 0 : inverseCausalInter / inverseCausalUnion;
        double concurrentSim = concurrentUnion == 0 ? 0 : concurrentInter / concurrentUnion;
        System.out.println(causalSim + " " + inverseCausalSim + " " + concurrentSim);
        return (float) ((causalSim + inverseCausalSim + concurrentSim) / 3);
    }
}
