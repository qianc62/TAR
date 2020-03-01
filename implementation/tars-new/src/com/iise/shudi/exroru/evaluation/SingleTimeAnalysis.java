package com.iise.shudi.exroru.evaluation;

//import cn.edu.thss.iise.beehivez.server.metric.mypetrinet.MyPetriNet;
//import cn.edu.thss.iise.beehivez.server.metric.mypetrinet.MyReachMarkingGraph;
//import cn.edu.thss.iise.beehivez.server.metric.mypetrinet.MyTransitionAdjacentRelationSet;
//import cn.edu.thss.iise.beehivez.server.metric.rorm.jbpt.conversion.PetriNetConversion;
//import cn.edu.thss.iise.beehivez.server.util.PetriNetUtil;
//import cn.edu.thss.iise.beehivez.server.util.TransitionLabelPair;

import com.iise.shudi.exroru.RefinedOrderingRelation;
import com.iise.shudi.exroru.RormSimilarity;

import org.jbpt.bp.RelSet;
import org.jbpt.bp.construct.ProjTARCreatorStateSpace;
import org.jbpt.petri.NetSystem;
import org.jbpt.petri.Node;
import org.jbpt.petri.Place;
import org.jbpt.petri.Transition;
import org.jbpt.petri.io.PNMLSerializer;
//import org.processmining.framework.models.petrinet.PetriNet;
//import org.processmining.framework.models.petrinet.algorithms.ReachabilityGraphBuilder;
//import org.processmining.importing.pnml.PnmlImport;
//import org.processmining.mining.petrinetmining.PetriNetResult;



import java.io.BufferedWriter;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.List;

class TaskRunner implements Runnable {
	
	NetSystem p,q;
	public long cpuTime = -1;
	public long ptarTime = -1;
	public long[] retVal = {-1,-1,-1,-1};
	WatchDog watcher = null;
	File currentFile = null;
	
	public TaskRunner(NetSystem p, File originalFile)
	{
		this.p = p;
		this.q = p;
		currentFile = originalFile;
	}
	
	public void stopRunning()
	{
		Thread.currentThread().interrupt();
		SingleTimeAnalysis.semiphore = true;
		System.out.println("try to interrupt");
	}
	
    public void run() {
    	RormSimilarity rorm = new RormSimilarity();
    	
        try {
			SingleTimeAnalysis.semiphore = false;
			SingleTimeAnalysis.isSafe = true;
			
			if (!currentFile.getName().contains("_Unbounded")) {
				long[] times1 = rorm.rormTest(p, q, false);  // to output detailed results, set the last argument as true 

				if (times1[0] < 40000000000L) {
					long[] times2 = rorm.rormTest(p, q, false);
					long[] times3 = rorm.rormTest(p, q, false);
					//long[] times4 = rorm.rormTest(p, q, false);
					//long[] times5 = rorm.rormTest(p, q, false);
					//times2 = rorm.rormTest(p, q, false);
					//times3 = rorm.rormTest(p, q, false);
					//times4 = rorm.rormTest(p, q, false);
					//times5 = rorm.rormTest(p, q, false);
					for (int i = 0; i < times1.length; i++) {
						times1[i] = (times2[i] + times3[i])/2;
					}
				}
				
				
				this.retVal = times1;
				this.cpuTime = times1[0];
				if (!currentFile.getName().contains("_PTARFailed") && !SingleTimeAnalysis.overRideFlag) {
	        		if (!SingleTimeAnalysis.semiphore) this.ptarTime = SingleTimeAnalysis.makePTAR(p, false);
	        		//else retVal[0]=-1;
				
	        		//if (!SingleTimeAnalysis.semiphore) this.ptarTime = SingleTimeAnalysis.makePTAR(p, false);
	        	}
			}
		} catch(InterruptedException e1) {
			if (retVal == null) System.out.println(p.getName() + "is unbounded");
			else System.out.println(p.getName() + "cannot be solved with reachability graph");
		}catch (Exception e) {
			// TODO Auto-generated catch block
			
			e.printStackTrace();
		} 
        
        if (SingleTimeAnalysis.semiphore) {
        	if (retVal[0] == -1) {
        		System.out.println(p.getName() + "is unbounded");
        	}
			else {
				ptarTime = -1;
				System.out.println(p.getName() + "cannot be solved with reachability graph");
			}
        }
        watcher.stopWatching();
    }
}

class WatchDog implements Runnable {

	TaskRunner toBeWatched = null;
	boolean stopped = false;
	
	public void stopWatching()
	{
		stopped = true;
		Thread.currentThread().interrupt();
		Thread.currentThread().interrupt();
		Thread.currentThread().interrupt();
	}
	
	public WatchDog(TaskRunner tr)
	{
		this.toBeWatched = tr;
	}
	
	public void run() {
	     	try {
				Thread.sleep(60000);
				if (!stopped && toBeWatched.retVal == null)
				{
					toBeWatched.stopRunning();
				}
				Thread.sleep(20000);
				if (!stopped && toBeWatched.ptarTime < 0) toBeWatched.stopRunning();
			} 	catch(InterruptedException e1) {
				
			}
	     	catch (Exception e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
	 }
}

public class SingleTimeAnalysis {
	public static boolean semiphore = false;
	public static boolean isSafe = true;
	public static boolean overRideFlag = false;
	
    public static final String ROOT_FOLDER = "F:\\tar\\";
//    public static final String ROOT_FOLDER = "E:\\wangshuhao\\Documents\\ExRORU\\";

    private Hashtable<String, File> fileMapping = new  Hashtable<String, File>();
    
	public static long startedTime;
	public static boolean failed = false;
    
	/*
    private void performZhaTAR(File theFile)
    {
		//String file2=System.getProperty("user.dir","")+"/Invisible2m.pnml";
		FileInputStream is1 = null;
		FileInputStream is2 = null;
		PetriNet pn1 =null;
		PetriNet pn2 =null;
		PnmlImport input = new PnmlImport();
		try {
			is1 = new FileInputStream(theFile);
			//is2 = new FileInputStream(file2);		
		} catch (FileNotFoundException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		try {
			pn1 = input.read(is1);
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		try {
			//pn2 = input.read(is2);
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
//		float res = sim.similarity(pn1, pn2);
//		System.out.println(res);
		
		MyTransitionAdjacentRelationSet tarSet1 = new MyTransitionAdjacentRelationSet(MyPetriNet.fromProMPetriToMyPetri(pn1));
    }
    */
    
    public static void main(String[] args) throws Exception {
        RefinedOrderingRelation.SDA_WEIGHT = 0.0;
        RefinedOrderingRelation.IMPORTANCE = true;
        SingleTimeAnalysis sta = new SingleTimeAnalysis();

        BufferedWriter writer = new BufferedWriter(new FileWriter(ROOT_FOLDER +
            "TAR_SingleTimeAnalysis_lib_b3_safetycheck.csv"));
        writer.write("model,cpu,tar,pure,pacc,ptar,tag,safe");
        writer.newLine();
        sta.analyze(writer);
        writer.close();
    }

    public void analyze(BufferedWriter writer) throws Exception {
        File[] dgFiles = new File(ROOT_FOLDER + "DG").listFiles();
        File[] tcFiles = new File(ROOT_FOLDER + "TC").listFiles();
        File[] sapFiles = new File(ROOT_FOLDER + "SAP").listFiles();
        File[] simpleFiles = new File(ROOT_FOLDER + "Simple").listFiles();
        File[] wlsFiles = new File(ROOT_FOLDER + "WLS").listFiles();
        File[] bpiFiles = new File(ROOT_FOLDER + "bpi").listFiles();
        File[] paraFiles = new File(ROOT_FOLDER + "para").listFiles();        
        File[] bpmFiles = new File(ROOT_FOLDER + "bpm").listFiles();    
        File[] beeFiles = new File(ROOT_FOLDER + "beehive1").listFiles();    

        File[] newspecial = new File(ROOT_FOLDER+"newspecial").listFiles();

        
        File[] lib_a2 = new File(ROOT_FOLDER+"lib_a2").listFiles();
        File[] lib_b2 = new File(ROOT_FOLDER+"lib_b2").listFiles();
        File[] lib_b3 = new File(ROOT_FOLDER+"lib_b3").listFiles();
        File[] lib_b4 = new File(ROOT_FOLDER+"lib_b4").listFiles();
        File[] lib_m1 = new File(ROOT_FOLDER+"lib_m1").listFiles();
        File[] lib_test = new File(ROOT_FOLDER+"test").listFiles();
        File[] lib_con = new File(ROOT_FOLDER+"con_scale_models").listFiles();
        File[] lib_serial = new File(ROOT_FOLDER+"con_serial_models").listFiles();
        File[] specialFiles = new File(ROOT_FOLDER+"special").listFiles();
        File[] lib_b2_safe = new File(ROOT_FOLDER+"lib_b2-1-safe").listFiles();
        File[] lib_b3_safe = new File(ROOT_FOLDER+"lib_b3-1-safe").listFiles();
        File[] lib_b4_safe = new File(ROOT_FOLDER+"lib_b4-1-safe").listFiles();
        File[] lib_a2_safe = new File(ROOT_FOLDER+"lib_a2-1-safe").listFiles();
        File[] lib_m1_safe = new File(ROOT_FOLDER+"lib_m1-1-safe").listFiles();
        
        // load net systems
       // List<NetSystem> dgNets = loadNets(dgFiles);
        //List<NetSystem> tcNets = loadNets(tcFiles);
       // List<NetSystem> sapNets = loadNets(sapFiles);
        //List<NetSystem> wlsNets = loadNets(wlsFiles);
        //List<NetSystem> simpleNets = loadNets(simpleFiles);
        //List<NetSystem> bpiNets = loadNets(bpiFiles);
        //List<NetSystem> paraNets = loadNets(paraFiles);
        //List<NetSystem> bpmNets = loadNets(bpmFiles);
        //List<NetSystem> beeNets = loadNets(beeFiles);
        
        
        List<NetSystem> lib_m1Nets =  loadNets(lib_m1);
        List<NetSystem> lib_b4Nets =  loadNets(lib_b4);
        List<NetSystem> lib_testNets = loadNets(lib_test);
        List<NetSystem> lib_b2Nets = loadNets(lib_b2);
        List<NetSystem> lib_b2_safeNets = loadNets(lib_b2_safe);
        List<NetSystem> lib_b3_safeNets =  loadNets(lib_b3_safe);
        List<NetSystem> lib_b4_safeNets =  loadNets(lib_b4_safe);
        List<NetSystem> lib_a2_safeNets =  loadNets(lib_a2_safe);
        List<NetSystem> lib_m1_safeNets =  loadNets(lib_m1_safe);
        
        
        //List<NetSystem> newspecialNets =  loadNets(newspecial);
        //List<NetSystem> lib_conNets = loadNets(lib_con);
        List<NetSystem> serialNets = loadNets(lib_serial);
        List<NetSystem> lib_serialConNets = loadNets(lib_serial);
        List<NetSystem> specialNets = loadNets(specialFiles);
        // compute time
        
        //computeTime(writer, simpleNets);
        //computeTime(writer, dgNets);
        //computeTime(writer, sapNets);
        //computeTime(writer, wlsNets);
        //computeTime(writer, tcNets);
        computeTime(writer, specialNets);
        //computeTime(writer, paraNets);
        //computeTime(writer, beeNets);
        //computeTime(writer, paraNets);
        //computeTime(writer, lib_conNets);
        //computeTime(writer, tcNets);
        //checkOneSafe(loadPetriNets(lib_a2));
        //this.makePTAR(wlsNets.get(0));
    }
    
    /*
    void checkOneSafe(List<PetriNet> pnets)
    {
    	List<PetriNet> safeList = new ArrayList<PetriNet>();

    	for (PetriNet pn : pnets) {
    		System.out.println("checking " + pn.getName());
    		ReachabilityGraphBuilder.build(pn);
    		if (ReachabilityGraphBuilder.isSafe) safeList.add(pn);
    	}
    	
    	for (PetriNet pn : safeList) {
    		System.out.println(pn.getName());
    	}
    }
    
    List<PetriNet> loadPetriNets(File[] files)
    {
    	List<PetriNet> retList = new ArrayList<PetriNet>();
    	for (File f : files) {
        	if (f.isDirectory())continue;
    		PnmlImport pImport = new PnmlImport();
    		PetriNetResult pnr = null;
    		FileInputStream fin = null;
    		try {
    			fin = new FileInputStream(f);
    			pnr = (PetriNetResult) pImport.importFile(fin);
    		} catch (IOException e) {
    			// TODO Auto-generated catch block
    			e.printStackTrace();
    		}
    		try {
    			if (fin != null) fin.close();
    		} catch (IOException e) {
    			// TODO Auto-generated catch block
    			e.printStackTrace();
    		}
    		PetriNet pn = pnr.getPetriNet();
    		retList.add(pn);
    		pn.setName(f.getAbsolutePath());
    	}
    	return retList;
    }*/
    
    private List<NetSystem> loadNets(File[] files) throws Exception {
        List<NetSystem> nets = new ArrayList<>();

        PNMLSerializer pnmlSerializer = new PNMLSerializer();
        //PnmlImport pnmlImport = new PnmlImport();
        for(int i = 0; i < files.length; ++i) {
        	if (files[i].isDirectory())continue;
            NetSystem net = pnmlSerializer.parse(files[i].getAbsolutePath());
            //PetriNet petrinet = pnmlImport.read(new FileInputStream(files[i]));
            //NetSystem ns = PetriNetConversion.convert(petrinet);
          
            for (Place p : net.getPlaces())
            {
    			if (net.getIncomingEdges(p) == null || net.getIncomingEdges(p).isEmpty()) {
    				net.getMarking().put(p, 1);
    			}
            }
            
            for (Transition t : net.getTransitions())
            {
            	//System.out.println(t.getName() + " v. " + t.getLabel() + " v. " + t.getId());   
            	if (t.getLabel().equals("")) t.setLabel(t.getId());
            }
            
            //ns.setName(files[i].getName());
            net.setName(files[i].getName());
            //this.fileMapping.put(ns.getName(), files[i]);
            this.fileMapping.put(net.getName(), files[i]);
            
            nets.add(net);
            //nets.add(ns);
        }
        return nets;
    }

    /*
     * Added by Jisheng
     * 2015 Aug. 13th
     */
    public static long makePTAR(NetSystem net, boolean outputOn)
    {
    	long start = System.nanoTime();
    	RelSet<NetSystem, Node> tarRelSet = ProjTARCreatorStateSpace.getInstance().deriveRelationSet(net, net.getNodes());
    	long ret = System.nanoTime() - start;
    	if (outputOn) System.out.println(tarRelSet);
    	return ret;
    }
    
    
    private void computeTime(BufferedWriter writer, List<NetSystem> nets) throws Exception {
        int totalCount = nets.size() * (nets.size() - 1) / 2, finish = 0;
        RormSimilarity rorm = new RormSimilarity();
        
        long totalTimeCPU = 0;
        long totalTimeConn = 0;
        long totalTimeTAR = 0;
        long totalTime_PTAR = 0;
        long totalTimePure = 0;
        long totalTimePureAcc = 0;
        long jinTotal = 0;
        long zhaTotal = 0;
    	
        int zhaFailedCount = 0;
        HashSet<String> safeFiles = new HashSet<String>();
        
        for(int p = 0; p < nets.size(); ++p) {
        	int q = p;
        	//for (int i = 0; i < 500; i++) {
        	
        	System.out.println((++finish) + "/" + totalCount + " " + nets.get(p).getName());
            //long[] times1 = rorm.similarityWithTime(nets.get(p), nets.get(q));

        	File currentFile = this.fileMapping.get(nets.get(p).getName());
            //if (Integer.parseInt(currentFile.getName().substring(0, currentFile.getName().length()-5)) > 12) overRideFlag = true;
            //else overRideFlag = false;
            
        	String tag = "";
            long[] times1 = {0,0,0,0};
            long timePTAR=0;
            
            /*
            if (!currentFile.getName().contains("_Unbounded")) {
				times1 = rorm.rormTest(nets.get(p), nets.get(p), false);
			
					long[] times2 = rorm.rormTest(nets.get(p), nets.get(p), false);
					long[] times3 = rorm.rormTest(nets.get(p), nets.get(p), false);
					//long[] times4 = rorm.rormTest(nets.get(p), nets.get(p), false);
					//long[] times5 = rorm.rormTest(p, q, false);
					times2 = rorm.rormTest(nets.get(p), nets.get(p), false);
					times3 = rorm.rormTest(nets.get(p), nets.get(p), false);
					//times4 = rorm.rormTest(nets.get(p), nets.get(p), false);
					//times5 = rorm.rormTest(p, q, false);
					for (int i = 0; i < times1.length; i++) {
						times1[i] = (times2[i] + times3[i])/2;
					}
					System.out.println(times2[0]);
					totalTimeCPU += times1[0];

				}
			*/	            
            /*
            if (!currentFile.getName().contains("_Unbounded")) {


            	PetriNet pn = PetriNetUtil.getPetriNetFromPnmlFile(currentFile);
            	
//            	HashSet<TransitionLabelPair> tlps = PetriNetUtil.getTARSFromPetriNetByCFP(pn);
            	performZhaTAR(currentFile);
            	
            	long start = System.nanoTime();
            	performZhaTAR(currentFile);
            	
            	//for (TransitionLabelPair tlp : tlps) {
            	//	System.out.println("Jin: " + tlp.getFirst() + "->" + tlp.getSecond());
            	//}
            	
            	

            	//rorm.rormTest(nets.get(p), nets.get(q), true);
            	if (MyTransitionAdjacentRelationSet.failed)  {
            		System.out.println("Zha Failed!");
            		MyTransitionAdjacentRelationSet.failed = false;
            		zhaFailedCount++;
            	}
            	else {
                	long aggregateTime = System.nanoTime() - start;
                	zhaTotal += aggregateTime;
                	safeFiles.add(currentFile.getName());
                	System.out.println("This Zha" + aggregateTime);
            	}
            	
                System.out.println("ZhaTotal:" + zhaTotal + "   Failed: " + zhaFailedCount + " times");
            }
            */
            
            /*
            if (!currentFile.getName().contains("_Unbounded") && !currentFile.getName().contains("6285")) {
            	PetriNet pn = PetriNetUtil.getPetriNetFromPnmlFile(currentFile);
            	//HashSet<TransitionLabelPair> tlps = PetriNetUtil.getTARSFromPetriNetByCFP(pn);
            	
            	long start = System.nanoTime();

            	HashSet<TransitionLabelPair> tlps = PetriNetUtil.getTARSFromPetriNetByCFP(pn);
            	
            	//for (TransitionLabelPair tlp : tlps) {
            	//	System.out.println("Jin: " + tlp.getFirst() + "->" + tlp.getSecond());
            	//}
            	
            	
            	long aggregateTime = System.nanoTime() - start;
            	jinTotal += aggregateTime;
            	//rorm.rormTest(nets.get(p), nets.get(q), true);
            	System.out.println("This JIN: " + aggregateTime);
                System.out.println("JinTotal:" + jinTotal);
            }
            */
            
        		TaskRunner  tr = new TaskRunner(nets.get(p),currentFile);
        		WatchDog wd = new WatchDog(tr);
        		tr.watcher = wd;
        	
        	
        	
        		Thread thread1 = new Thread(tr);
        		Thread thread2 = new Thread(wd);
        		thread2.start();
        		thread1.start();
        		thread1.join();
        	
        		//long[] times1 = rorm.rormTest(nets.get(p), nets.get(q),true); 
        		times1 = tr.retVal;
        		totalTimeCPU += times1[0];
        		
        		//DEPRECATED OLD
        		//totalTimeTAR += times1[1];
           
        		//if (times1[0]<1000000000L * 2L) {
        		timePTAR = tr.ptarTime;
            	//timePTAR = makePTAR(nets.get(p), false);
            	//timePTAR = makePTAR(nets.get(p), false);
        		//	 }
            

            
        		if (times1[0] == -1 && !currentFile.getName().contains("_Unbounded")) {
        			File newFile = new File(currentFile.getParentFile().getAbsolutePath() + "/" + currentFile.getName() + "_Unbounded");
        			tag = "Unbounded";
        			currentFile.renameTo(newFile);
        		}
        		else if (timePTAR == -1 && !currentFile.getName().contains("_PTARFailed")) {
        			File newFile = new File(currentFile.getParentFile().getAbsolutePath() + "/" + currentFile.getName() + "_PTARFailed");
        			currentFile.renameTo(newFile);
        			tag = "PTARFailed";
        		}
        	
        	
        		totalTime_PTAR += timePTAR;
            
        		totalTimePure += times1[2];
        		totalTimePureAcc += times1[3];
                //System.out.println("Total Pure Time:" + totalTimePure);
                //System.out.println("Total PAcc Time:" + totalTimePureAcc);

        		System.out.println("CPU-BUILD: " + times1[0]);
        		//System.out.println("DEPRECATED-IMPLEMENTATION(OLD): " + times1[1]);
        		System.out.println("  GENERAL: " + times1[2]);
        		System.out.println(" IMRPOVED: " + times1[3]);
        		System.out.println(" RG-BASED: " + timePTAR);
        		//if (times1[0]<timePTAR) System.out.println("!!!!!!!!");
        		//if (times1[0] < timePTAR)
        		//{
        			//System.out.println(nets.get(p).getName());
        		//}
        	
        	if (currentFile.getName().contains("_Unbounded")) tag = "Unbounded";
        	if (currentFile.getName().contains("_PTARFailed")) tag = "PTARFailed";
        	String safeStr = "1-safe";
        	if (SingleTimeAnalysis.isSafe) safeStr = "Unsafe";
        	writer.write(currentFile.getName() + "," + times1[0] + "," + times1[1] + "," + times1[2] + "," + times1[3] + "," + timePTAR + "," + tag + "," + safeStr);

            writer.newLine();
          
        	//}
        	
        //}
        }
       
       

       /*
        for(int p = 0; p < nets.size(); ++p) {
            int q = p;
        	//for(int q = p + 1; q < nets.size(); ++q) {
                System.out.println((++finish) + "/" + totalCount + " " + nets.get(p).getName() + " & " + nets.get(q).getName());
                long[] times1 = rorm.similarityWithTime(nets.get(p), nets.get(q));
                long[] times2 = rorm.similarityWithTime(nets.get(p), nets.get(q));
                long[] times3 = rorm.similarityWithTime(nets.get(p), nets.get(q));
                long[] times4 = rorm.similarityWithTime(nets.get(p), nets.get(q));
                long[] times5 = rorm.similarityWithTime(nets.get(p), nets.get(q));
                long[] times = new long[times1.length];
                for (int i = 0; i < times.length; ++i) {
                    times[i] = (times1[i] + times2[i] + times3[i] + times4[i] + times5[i]) / 5;
                }
                
                long timeCPU = times[1] + times[7];
                //long timeTAR = times[2] + times[8];
                long timeConn = times[1] + times[7] + times[2] + times[8] + times[4] + times[10];
                
                totalTimeCPU += timeCPU;
                //totalTimeTAR += timeTAR;
                totalTimeConn += timeConn;
                
                writer.write(nets.get(p).getName() + " & " + nets.get(q).getName());
                for (long t : times) {
                    writer.write("," + t);
                }
                writer.newLine();
            //}
        }*/
        System.out.println("CPU  Time:" + totalTimeCPU);
        //System.out.println("DEPRECATED TAR (OLD IMPLEMENTATION) Time:" + totalTimeTAR);
        System.out.println("  RG Time:" + totalTime_PTAR);
        System.out.println("  GENERAL:" + totalTimePure);
        System.out.println(" IMPROVED:" + totalTimePureAcc);

        //System.out.println("TAR Time:" + totalTimeTAR);
        /*System.out.println("Rate:" + (double)((double)totalTimeTAR/(double)totalTimeCPU));*/
        /*
        System.out.println("Safe Files:");
        for (String str : safeFiles)
        {
        	System.out.println(str);
        }*/
    }
}
