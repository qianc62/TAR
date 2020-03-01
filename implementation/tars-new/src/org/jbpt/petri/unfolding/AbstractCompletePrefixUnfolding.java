package org.jbpt.petri.unfolding;

import org.jbpt.petri.*;
import org.jbpt.petri.unfolding.order.*;

import com.iise.shudi.exroru.evaluation.SingleTimeAnalysis;

import java.util.*;


/**
 * (An abstract) implementation of a complete prefix unfloding of a net system.<br/><br/>
 * <p>
 * This class implements techniques described in:
 * - Javier Esparza, Stefan Roemer, Walter Vogler: An Improvement of McMillan's Unfolding Algorithm. Formal Methods in System Design (FMSD) 20(3):285-310 (2002).
 * - Victor Khomenko: Model Checking Based on Prefixes of Petri Net Unfoldings. PhD Thesis. February (2003).
 *
 * @author Artem Polyvyanyy
 */
public class AbstractCompletePrefixUnfolding<BPN extends IBPNode<N>, C extends ICondition<BPN, C, E, F, N, P, T, M>, E extends IEvent<BPN, C, E, F, N, P, T, M>, F extends IFlow<N>, N extends INode, P extends IPlace, T extends ITransition, M extends IMarking<F, N, P, T>>
        extends AbstractBranchingProcess<BPN, C, E, F, N, P, T, M>
        implements ICompletePrefixUnfolding<BPN, C, E, F, N, P, T, M> {

    // setup to use when constructing this complete prefix unfolding
    protected CompletePrefixUnfoldingSetup setup = null;
    // map of cutoff events to corresponding events
    protected Map<E, E> cutoff2corr = new HashMap<E, E>();
    // total order used to construct this complete prefix unfolding
    protected List<T> totalOrderTs = null;
    // adequate order used to construct this complete prefix unfolding
    protected IAdequateOrder<BPN, C, E, F, N, P, T, M> ADEQUATE_ORDER = null;
    // set of possible extensions updates
    private Set<E> UPE = null;

    private Set<E> invisibleSet;
    
    private HashSet<E> traverseEventUsed = new HashSet<E>();
    
    private Hashtable<String,Set<String>> pureTARs;
    private Hashtable<String,Set<String>> pureTARsAccelerated;
    
    private long pureTARTime;
    private long pureAcceleratedTARTime;    
    /**
     * Empty constructor.
     */
    protected AbstractCompletePrefixUnfolding() {
    }

    /**
     * Constructor with default setup.
     *
     * @param sys Net system to construct complete prefix unfolding for.
     */
    public AbstractCompletePrefixUnfolding(INetSystem<F, N, P, T, M> sys) {
        this(sys, new CompletePrefixUnfoldingSetup());
    }

    /**
     * Constructor with specified setup.
     *
     * @param sys   Net system to construct complete prefix unfolding for.
     * @param setup Setup to use when constructing complete prefix unfolding.
     */
    public AbstractCompletePrefixUnfolding(INetSystem<F, N, P, T, M> sys, CompletePrefixUnfoldingSetup setup) {
        super(sys);

        // net system must be different from null
        if (this.sys == null) return;
        // initial branching process must not be empty
        this.constructInitialBranchingProcess();
        if (this.iniBP.isEmpty()) return;

        // initialise
        this.totalOrderTs = new ArrayList<T>(sys.getTransitions());
        this.setup = setup;

        switch (this.setup.ADEQUATE_ORDER) {
            case ESPARZA_FOR_ARBITRARY_SYSTEMS:
                this.ADEQUATE_ORDER = new EsparzaAdequateOrderForArbitrarySystems<BPN, C, E, F, N, P, T, M>();
                break;
            case ESPARZA_FOR_SAFE_SYSTEMS:
                this.ADEQUATE_ORDER = new EsparzaAdequateTotalOrderForSafeSystems<BPN, C, E, F, N, P, T, M>();
                break;
            case MCMILLAN:
                this.ADEQUATE_ORDER = new McMillanAdequateOrder<BPN, C, E, F, N, P, T, M>();
                break;
            case UNFOLDING:
                this.ADEQUATE_ORDER = new UnfoldingAdequateOrder<BPN, C, E, F, N, P, T, M>();
                break;
            default:
                this.ADEQUATE_ORDER = new EsparzaAdequateTotalOrderForSafeSystems<BPN, C, E, F, N, P, T, M>();
                break;
        }

        // construct unfolding
        if (this.setup.SAFE_OPTIMIZATION)
            this.constructSafe();
        else
            this.constructSafe();
    }

    /*
     * Added by Jisheng
     * Check if an event corresponds to an invisible task according to its label prefix
     * 08/10/2015
     */
    private boolean isInvisibleEvent(E event)
    {
    	if (event.getTransition().getLabel().startsWith("inv_") || event.getTransition().getLabel().equals(""))
    	//if (event.getTransition().getLabel().equals(""))
    	{
    		return true;
    	}
    	else
    		return false;
    }
    
    /*
     * Added by Jisheng
     * Return the 'root' corresponding event of a cut-off event
     * 08/10/2015
     */
    private E getRootCorr(E e)
    {
    	E rootCorr = this.cutoff2corr.get(e);
        while (this.cutoff2corr.containsKey(rootCorr)) { 
            rootCorr = this.cutoff2corr.get(rootCorr);  
        }
        return rootCorr;
    }
    
    /*
     * Added by Jisheng
     * Check if a non-cut-off event has corresponding invisible tasks 
     * This is to detect possible 'jumps' across non-invisible events during 'direct or invisible' reach-ability test
     * 08/10/2015
     */
    private E hasInvisibleCorr(E e)
    {
    	boolean hit = false;
    	E ret = null;
    	for (E ce : this.invisibleSet)
		{
			if (this.cutoff2corr.get(ce)!= null){
	        	E rootCorr = this.cutoff2corr.get(ce);
	            if (rootCorr == e) hit = true;
	            while (this.cutoff2corr.containsKey(rootCorr)) { 
	                rootCorr = this.cutoff2corr.get(rootCorr);  
		            if (rootCorr == e) hit = true;
	            }
	            ret = rootCorr;
			}
				
		}
    	
    	if (!hit) return null;
    	else
    		return ret;
    }
    
    /*
     * This is to check if there exists a path connecting #startingCondition# and #destinationCondition#
     * that are entirely made up of condition(s) and invisible event(s) (if any).
     * As this is to help check whether there exists a third event that 'blocks' the way between the above two 
     * conditions (see existNoThirdEvent function below), those paths which does not lead to the #destinationCondition# could be safely ignored.
     * We achieve this by stopping the expansion once we find an event to be extended has no causal relationship
     * with the #destinationCondition#.
     * Jisheng 08/10/2015
     */
    private boolean isDirectlyOrInvReachable(C startingCondition, C destinationCondition)
    {

   		if (startingCondition == destinationCondition) return true;   // if directly reachable (identical) then return true
   		
   		
   		Set<E> postEventSet = startingCondition.getPostE(); // enumerate through paths leading from all post-events

   		for (E postEvent : postEventSet) {
   			
   			E rootCorr;
   			
   			if (cutoff2corr.get(postEvent) != null) // for cut-off events, which generally do not have succeeding conditions, 
   													// we map them to their root corresponding event.
   			{
   				rootCorr= this.getRootCorr(postEvent);
   				//if (this.areCausal((BPN)rootCorr, (BPN)postEvent)) continue;  // avoid infinite loop

   				postEvent = rootCorr;
   			}
   				
    		if (!isInvisibleEvent(postEvent) && hasInvisibleCorr(postEvent) == null) continue; 
    			// if it were part of a DOI path, the event must be related to an invisible task itself, or it has corresponding events that are invisible

    		/*
    			E rootCorr = hasInvisibleCorr(postEvent);
    			if (rootCorr != null) 
    			{
    				if (this.areCausal((BPN)rootCorr, (BPN)postEvent)) continue;
    				//postEvent = hasInvisibleCorr(postEvent);
    				if (!this.areCausal((BPN)rootCorr, (BPN)destinationCondition)) continue;
        	    	for (C postPostCond : rootCorr.getPostConditions())
        	    	{
        	    		if (isDirectlyOrInvReachable(postPostCond, destinationCondition)) return true;   // if eventually reachable
        	    	}
        	    	continue;
    			}
    		
    		*/
    		
    		// if the event has no causal relationship with the destination event,
    		// it will be not necessary to look further down into this branch   		
   			//if (!this.areCausal((BPN)postEvent, (BPN)destinationCondition)) continue;
   			
    		if (this.traverseEventUsed.contains(postEvent)) continue;
   			
   			this.traverseEventUsed.add(postEvent);
   			
   			// extend further into this branch
   			// if any DOI path discovered, return successful
   	    	for (C postPostCond : postEvent.getPostConditions())
   	    	{
   	    		if (isDirectlyOrInvReachable(postPostCond, destinationCondition))
   	    		{
   	    	    	this.traverseEventUsed.remove(postEvent);
   	    			return true;   // if eventually reachable	
   	    		}
   	    	}
   	    	
   	    	this.traverseEventUsed.remove(postEvent);
    	}
    	
    	return false; // otherwise...
    }
    
    private boolean existNoThirdEvent(E startingEvent, ICoSet<BPN, C, E, F, N, P, T, M> sinkPreConditions) //isTar is changed into existNoThirdEvent
    {
    	for (C cSource : startingEvent.getPostConditions())
    	{
    		for (C cSink : sinkPreConditions)
    		{
    			if (this.areCausal((BPN)cSource, (BPN)cSink)) // if they are causal, there must be a path (or paths) connecting between these two conditions
    			{
    				if (isDirectlyOrInvReachable(cSource, cSink)) continue; // if TAR relation exists, there must be at least one DOI path to explain the causal relationship of these two conditions
    				//if (cSource.getPlace().equals(cSink.getPlace())) continue;
    				return false;
    			}
    		}
    	}
    	return true;
    }
    
    private boolean isMaxEvent(E e, ICoSet<BPN, C, E, F, N, P, T, M> sinkPreConditions)
    {
    	for (C c: e.getPostConditions())
    	{
    		if (this.areCausal((BPN)c, (BPN)e))
    		{
    			if (!e.getPreConditions().contains(c)) return false;
    		}
    	}
    	return true;
    }
    
    private Set<E> findPureMaxEventAdjacency(E sinkEvent)
    {
    	Set<E> sourceEventsForE = new HashSet<E>();
    	
    	ICoSet<BPN, C, E, F, N, P, T, M> sinkPreConditions = sinkEvent.getPreConditions();
    	
    	for (C c : sinkPreConditions) {
            E e = c.getPreEvent();
            if (e == null) continue;  // starting event?
            
            if (isMaxEvent(e, sinkPreConditions))
            {
            	sourceEventsForE.add(e);
            }
    	}   	  
    	
    	return sourceEventsForE;
    	
    }
    
    /*
     * Find directly connected TARs (partially considering INV events, but not all those that are entirely connected by INV paths)
     */
    private Set<E> findTar(E sinkEvent) 
    {
    	Set<E> sourceEventsForE = new HashSet<E>();
    	
    	ICoSet<BPN, C, E, F, N, P, T, M> sinkPreConditions = sinkEvent.getPreConditions();
    	
    	for (C c : sinkPreConditions) {
            E e = c.getPreEvent();
            if (e == null) continue;  // starting event?
            
            if (existNoThirdEvent(e, sinkPreConditions))
            {
            	sourceEventsForE.add(e);
            }
    	}   	  
    	
    	return sourceEventsForE;
    	  
    }
       
    /*
     * Back-tracking all the possible TAR source events along 'invisible paths', INCLUDING invisible source events
     */
    private Set<E> getInvPathEvents(E sinkEvent)
    {
    	Set<E> invPathEvents = new HashSet<E>();
    	
    	if (this.traverseEventUsed.contains(sinkEvent)) return invPathEvents;
    	
    	this.traverseEventUsed.add(sinkEvent);
    	
    	for (C c : sinkEvent.getPreConditions()) {
    		E preEvent = c.getPreEvent();
    		
    		if (!isInvisibleEvent(preEvent)) {
    			invPathEvents.add(preEvent);
    		}
    		else {
    			invPathEvents.add(preEvent);
    			invPathEvents.addAll(getInvPathEvents(preEvent));
    		}
    		
    		for (E ce : this.invisibleSet)
			{
				if (this.cutoff2corr.get(ce)!= null){
		        	E rootCorr = this.cutoff2corr.get(ce);
		        	
		            while (this.cutoff2corr.containsKey(rootCorr)) { 
		                rootCorr = this.cutoff2corr.get(rootCorr);  
		            }
		            /*
		             * here we calculate the root corr of all invisible events to see if 
		             * there are invisible events that are in correspondence with the current event,
		             * so as to 'jump' across non-invisible events in such cases
		             */
		            //TODO:  This is not efficient! An mapping structure should be introduced to avoid repeatedly testing
		            
//		            if (rootCorr == preEvent && this.areCausal((BPN)ce, (BPN)sinkEvent)) invPathEvents.addAll(getInvPathEvents(ce));
		            /*
		            if (rootCorr == preEvent && (existNoThirdEvent(sinkEvent, ce.getPreConditions()))) {
		            	System.out.println(sinkEvent);
		            	System.out.println(ce);
		            	
		            }*/
		            		
		            if (rootCorr == preEvent) invPathEvents.addAll(getInvPathEvents(ce));
				}
					
			}

    	}
    	
    	this.traverseEventUsed.remove(sinkEvent);
    	return invPathEvents;
    }
    
    private void makeConcurrentTAR()
    {
    	for (E e : this.events)
    	{
    		for (E ee : this.events)
    		{
    			if (e == ee) continue;
    			if (this.areConcurrent((BPN)e, (BPN)ee))
    			{
    				if (this.tar.get(e) == null)
	        			this.tar.put(e, new HashSet<E>());
	        		this.tar.get(e).add(ee); 
    			}
    		}
    	}
    }
    
    private void checkInvCausedTAR()
    {	
    	for (E invE : this.invisibleSet) { 
    		
    			if (cutoff2corr.get(invE) != null) // if #invE# is a cut-off event, we need to switch to its corresponding event to find post events
    			{
    				invE = this.getRootCorr(invE); // note that now invE may not necessarily be an invisible event (in that case, it corresponds to one)
    			}
    			
    			for (E e : tar.get(invE)) {
    				if (!isInvisibleEvent(e)) // such that e is a VISIBLE event with at least one INVISIBLE event ancestor
    				{
    					ICoSet<BPN, C, E, F, N, P, T, M> sinkPreConditions = e.getPreConditions(); 
    										// we shall check for any invisible-event-caused TAR that has #e# as the sink event
    										// therefore we prepare #e#'s preconditions first for the up-coming reach-ability tests
    					Set<E> preEvents = getInvPathEvents(e); // get pre-events connected with an 'invisible path'
    					for (E sourceE : preEvents) {
    						E eventToStartWith = sourceE;
    						
    						if (cutoff2corr.get(sourceE) != null) eventToStartWith = this.getRootCorr(sourceE); 
    														// if the candidate is a cut-off event, we need to switch to the main stream for reach-ability check
    						//if (this.areCausal((BPN)eventToStartWith, (BPN)sourceE)) eventToStartWith = sourceE;
    														// however, if infinite-loop is expected, we stick to the original candidate
        					if (existNoThirdEvent(eventToStartWith, sinkPreConditions)) // if the no-third-exist condition is satisfied
        					{
        		        		if (this.tar.get(sourceE) == null)
        		        			this.tar.put(sourceE, new HashSet<E>());
        		        		this.tar.get(sourceE).add(e);  //then add the #e# as #sourceE#'s sink event
        					}
    						
    					}
    				}
    			}
    		
    	}
    	System.out.println();
    }
    
    /*
     *  Calculating sequential tars (tars involving cut-off event not considered yet)
     *  by jisheng 15/08/09
     */
    private void checkNormalSequentialTAR(E e)
    {
        Set<E> tarSourceSet = findTar(e);				// find all preceding tar sources			
        if (tarSourceSet.size() > 0) {
        	for (E sourceE : tarSourceSet)
        	{
        		if (this.tar.get(sourceE) == null)
        			this.tar.put(sourceE, new HashSet<E>());
        		this.tar.get(sourceE).add(e);
        	}
        }
    }
    /*
     * jisheng: cut-off-free tar handling ends here
     */
    
    /*
     * added by jisheng 15/08/09
     * handling tars involving cut-off events
     */
    private void checkCutOffSequentialTAR()
    {
        for (E cutOffE : this.cutoff2corr.keySet())
        {
        	E rootCorr = this.cutoff2corr.get(cutOffE);
        	
            while (this.cutoff2corr.containsKey(rootCorr)) { // a cut-off event may actually be corresponded to a series of other cut-off events
                rootCorr = this.cutoff2corr.get(rootCorr);   // for TAR calculation we need only to determine the 'root' (earliest) corresponding event
            }
            
            ICoSet<BPN, C, E, F, N, P, T, M> ePostConds = cutOffE.getPostConditions(); 
            								// get the set of post conditions of the cut-off event
                        
         /*
          *  For each sink event #tarSinkEvent# that are in TAR relation with the 'root' corresponding event #rootCorr# 
          *  (that is to say, <#rootCorr#, #tarSinkEvent#> is a TAR relation),
          *  we check that if #tarSinkEvent# is actually reachable from the cut-off event #cutOffE#.
          *  This is to avoid the special cases in which even though #cutOffE# and #rootCorr# are corresponded,
          *  #tarSinkEvent# is not reachable from #cutOffE#.
          */
            for (E tarSinkEvent : this.tar.get(rootCorr)) 
            {
            	for (C cutOffEPostCondition : ePostConds)
            	{
            		boolean flag = false;
            		for (C tarSinkPreCondition : tarSinkEvent.getPreConditions()) { //0810 added for inv+cut-off
            			if (isDirectlyOrInvReachable(cutOffEPostCondition.getCorrespondingCondition(), tarSinkPreCondition)) { //0810 added for inv+cut-off
            		//if (tarSinkEvent.getPreConditions().contains(cutOffEPostCondition.getCorrespondingCondition())) // if directly reachable
            		//{
            				if (this.tar.get(cutOffE) == null)
            					this.tar.put(cutOffE, new HashSet<E>());
            				this.tar.get(cutOffE).add(tarSinkEvent); // a new tar relation <#cutOffE#, #tarSinkEvent#> is added
            				flag = true;
            				break;
            			}
            		//}
            		}
            		if (flag) break; // flag for double break
            	}
            }
        }
    }
    /*
     * jisheng: cut-off tars handling ends here
     */
    
    boolean recurrenceCheck(T t, C c)
    {
    	if (c.getPreEvent() == null) return false;
    	if (c.getPreEvent().getTransition().getLabel().equals(t.getLabel())) return true;
    	for (C cc : c.getPreEvent().getPreConditions()) {
    		if (recurrenceCheck(t,cc)) 
    			return true;
    	}
    	return false;
    }
    
    protected void constructSafe() {
    	
        
        IPossibleExtensions<BPN, C, E, F, N, P, T, M> pe = getInitialPossibleExtensions();    // get possible extensions of the initial branching process
    	//long start = System.nanoTime();

        while (!pe.isEmpty()) {                                        // while extensions exist
        	if (SingleTimeAnalysis.semiphore) break;
        	if (this.events.size() >= this.setup.MAX_EVENTS) return;    // track number of events in unfolding
            E e = pe.getMinimal();                                        // event to use for extending unfolding
            pe.remove(e);                                                // remove 'e' from the set of possible extensions
            if (!this.appendEvent(e)) return;                            // add event 'e' to unfolding

            E corr = this.checkCutoffA(e);                                // check if 'e' is a cutoff event
            if (corr != null)
            {
                this.addCutoff(e, corr);                                    // record cutoff
            }
            else
            	pe.addAll(this.updatePossibleExtensions(e));

        }
        
        /*
        for (E e : this.events)
        {
        	checkNormalSequentialTAR(e);
        }
        checkCutOffSequentialTAR();
         */
        
    }
    
    private boolean enumerateClique(Hashtable<P,Set<C>> coverMapping, Set<C> usedConditions, Set<P> coveredPlaces)
    {
    	if (usedConditions.size() == coverMapping.size()) return true;
    	
    	Iterator<P> iter = coverMapping.keySet().iterator();
    	while(iter.hasNext())
    	{
    		P p = iter.next();
    		if (!coveredPlaces.contains(p))
    		{
    			for (C c : coverMapping.get(p))
    			{
    				usedConditions.add(c);
    				if (this.areMutuallyConcurrent(usedConditions)) {
    					coveredPlaces.add(c.getPlace());
    					if (enumerateClique(coverMapping, usedConditions, coveredPlaces)) return true;
    					coveredPlaces.remove(c.getPlace());
    				}
					usedConditions.remove(c);
    			}
    			break;
    		}
    	}
    	return false;
    }
    
    private boolean checkByClique(T t1, T t2)
    {
    	Set<E> h_events_t1 = this.getEvents(t1);
		Set<E> h_events_t2 = this.getEvents(t2);
		Set<C> frontierConditions = new HashSet<C>();
		Set<C> candidateConditions = new HashSet<C>();
		Set<P> placesToBeCovered = new HashSet<P>();
		
		for (E e2 : h_events_t2) {
			placesToBeCovered.addAll(this.getPlaces(e2.getPreConditions()));
			break;
		}
		
		for (P p : placesToBeCovered) {
			frontierConditions.addAll(this.getConditions(p));
		}
		
		Hashtable<P,Set<C>> coverMapping = new Hashtable<P,Set<C>>();
		
		for (E e1 : h_events_t1) {

			for (C c : frontierConditions) {
				if (this.areConcurrent((BPN) c, (BPN)e1) || e1.getPostConditions().contains(c)) {

					P place = c.getPlace();
					
					if (coverMapping.get(place) == null)
					{
						Set<C> conditions = new HashSet<C>();
						conditions.add(c);
						coverMapping.put(c.getPlace(), conditions);
					}
					else
					{
						coverMapping.get(place).add(c);
					}
				}
			}
			
			if (coverMapping.size() == placesToBeCovered.size()) {
				if (coverMapping.size() != 0 && enumerateClique(coverMapping, new HashSet<C>(),new HashSet<P>())) return true;
			}
			
			coverMapping.clear();
		}
		
		return false;
    }
    
    public Hashtable<String,Set<String>> getPureTARs()
    {
    	return this.pureTARs;
    }
    
    public long getPureTARTime()
    {
    	return this.pureTARTime;
    }
    
    public long getPureAccleratedTARTime()
    {
    	return this.pureAcceleratedTARTime;
    }
    
    public Hashtable<String,Set<String>> getPureTAR_Accelerated()
    {
    	return this.pureTARsAccelerated;
    }
    
    public long makePureTAR_Accelerated()
    {
    	Set<E> events = this.getEvents();
    	Hashtable<String,Set<String>> foundTARs = new Hashtable<String,Set<String>>();
    	Set<T> transitions = this.sys.getTransitions();
    	Hashtable<T,HashSet<T>> toBeConfirmed = new Hashtable<T,HashSet<T>>();
    	
    	for (T t1 : transitions) {
       		Set<P> successors = this.sys.getPostset(t1);
       		for (P p : successors) {
       			for (T t2: this.sys.getPostset(p))
       			{
    				HashSet<T> postSetTrans = toBeConfirmed.get(t1);
    				if (postSetTrans == null) postSetTrans = new HashSet<T>();
    				postSetTrans.add(t2);
    				toBeConfirmed.put(t1, postSetTrans);
       			}
       			
       		}
       	}
    	
    	long start = System.nanoTime();
    	
    	for (E e1 : events) {
    		for (E e2 : events) {
    			if (e1 == e2) continue;
    			if (this.areConcurrent((BPN)e1, (BPN)e2))
    			{
    				T t1 = e1.getTransition();
					T t2 = e2.getTransition();
					if (foundTARs.get(t1.getLabel()) == null) {
    					HashSet<String> tarSet = new HashSet<String>();
    					tarSet.add(t2.getLabel());
    					foundTARs.put(t1.getLabel(), tarSet);
    				}
    				else foundTARs.get(t1.getLabel()).add(t2.getLabel());
    			}
    		}
    	}
    	

    	for (E e1 : events) {
    		Set<C> postConditions;
    		if (this.isCutoffEvent(e1))
    		{
    			Set<P> places = this.getPlaces(e1.getPostConditions());
    			E corrE = this.getRootCorr(e1);
    			if (this.getPlaces(corrE.getPostConditions()).equals(places)) {
    				postConditions = corrE.getPostConditions();
    			}
    			else continue;
    		}
    		else postConditions = e1.getPostConditions();
    		
    		T precTran = e1.getTransition();
    		
    		for (C c : postConditions) {
    			for (E e2 : c.getPostE()) {
    				
    				boolean flag = true;
    				Set<C> e2preConditions = e2.getPreConditions();

    				for (C e1pc : postConditions) {
    					if (this.areCausal((BPN)e1pc, (BPN)e2))
    					{
    						if (!e2preConditions.contains(e1pc)) {
    							flag = false;
    							break;
    						}
    					}
    				}
    				
    				if (flag) { // max-event adjacent!
    					T t1 = e1.getTransition();
    					T t2 = e2.getTransition();
    					if (foundTARs.get(t1.getLabel()) == null) {
        					HashSet<String> tarSet = new HashSet<String>();
        					tarSet.add(t2.getLabel());
        					foundTARs.put(t1.getLabel(), tarSet);
        				}
        				else foundTARs.get(t1.getLabel()).add(t2.getLabel());
    					toBeConfirmed.get(precTran).remove(e2.getTransition());
    				}
    			}
    		}
    	}
    	
    	for (T t1 : toBeConfirmed.keySet())
    	{
    		for (T t2 : toBeConfirmed.get(t1))
    		{
    			 this.sys.getPostset(t1);
					if (this.checkByClique(t1, t2)) {
   	    				if (foundTARs.get(t1.getLabel()) == null) {
   	    					HashSet<String> tarSet = new HashSet<String>();
   	    					tarSet.add(t2.getLabel());
   	    					foundTARs.put(t1.getLabel(), tarSet);
   	    				}
   	    				else foundTARs.get(t1.getLabel()).add(t2.getLabel());
   	    			}
    		}
    	}
    	
    	/*
       	for (T t1 : transitions) {
       		Set<P> successors = this.sys.getPostset(t1);
       		for (P p : successors) {
       			for (T t2: this.sys.getPostset(p))
       			{
       				if (foundTARs.get(t1) == null || !foundTARs.get(t1).contains(t2))
       				{
       					if (this.checkByClique(t1, t2)) {
       	    				if (foundTARs.get(t1.getLabel()) == null) {
       	    					HashSet<String> tarSet = new HashSet<String>();
       	    					tarSet.add(t2.getLabel());
       	    					foundTARs.put(t1.getLabel(), tarSet);
       	    				}
       	    				else foundTARs.get(t1.getLabel()).add(t2.getLabel());
       	    			}
       				}
       			}
       			
       		}
       	}*/
       	 
    	long endTime = System.nanoTime() - start;

       	this.pureTARsAccelerated = foundTARs;
       	this.pureAcceleratedTARTime = endTime;
    	return endTime;
    }
    
    public Hashtable<String,Set<String>> makePureTAR()
    {
    	long start = System.nanoTime();

    	Hashtable<String,Set<String>> foundTARs = new Hashtable<String,Set<String>>();
    	
    	Set<T> transitions = this.sys.getTransitions();
    	for (T t1 : transitions) {
    		for (T t2: transitions) {
    			if (this.checkByClique(t1, t2)) {
    				if (foundTARs.get(t1.getLabel()) == null) {
    					HashSet<String> tarSet = new HashSet<String>();
    					tarSet.add(t2.getLabel());
    					foundTARs.put(t1.getLabel(), tarSet);
    				}
    				else foundTARs.get(t1.getLabel()).add(t2.getLabel());
    			}
    		}
    	}
    	long endTime = System.nanoTime() - start;
    	this.pureTARTime = endTime;
    	
    	this.pureTARs = foundTARs;
    	return foundTARs;    	
    }
    
    public void makeTAR()
    {
    	invisibleSet = new HashSet<E>();
    	for (E ce : this.events) if (isInvisibleEvent(ce)) invisibleSet.add(ce);
        for (E e : this.events)
        {
        	checkNormalSequentialTAR(e);
        }
        //checkCutOffSequentialTAR();
        checkInvCausedTAR();
        checkCutOffSequentialTAR();
        makeConcurrentTAR();
    }
    
    // map a condition to a set of cuts that contain the condition
    //protected Map<C,Collection<ICut<P,T,C,E>>> c2cut = new HashMap<C,Collection<ICut<P,T,C,E>>>();
    // maps of transitions/places to sets of events/conditions (occurrences of transitions/places)
    //protected Map<T,Set<E>> t2es	= new HashMap<T,Set<E>>();
    //protected Map<P,Set<C>> p2cs	= new HashMap<P,Set<C>>();

    /**
     * Construct unfolding.
     * <p>
     * This method closely follows the algorithm described in:
     * Javier Esparza, Stefan Roemer, Walter Vogler: An Improvement of McMillan's Unfolding Algorithm. Formal Methods in System Design (FMSD) 20(3):285-310 (2002).
     */
    /*protected void construct() {
        if (this.sys==null) return;

		// CONSTRUCT INITIAL BRANCHING PROCESS
		M M0 = this.sys.getMarking();
		for (P p : this.sys.getMarking().toMultiSet()) {
			C c = this.createCondition(p,null);
			this.addCondition(c);
			this.initialBranchingProcess.add(c);
		}
		if (!this.addCut(initialBranchingProcess)) return;
		
		//  Event cutoffIni = null; Event corrIni = null;				// for special handling of events that induce initial markings
		
		// CONSTRUCT UNFOLDING
		Set<Event> pe = getPossibleExtensionsA();						// get possible extensions of initial branching process
		while (!pe.isEmpty()) { 										// while extensions exist
			if (this.countEvents>=this.setup.MAX_EVENTS) return;		// track number of events in unfolding
			Event e = this.setup.ADEQUATE_ORDER.getMinimal(pe);			// event to use for extending unfolding
			
			if (!this.overlap(cutoff2corr.keySet(),e.getLocalConfiguration())) {
				if (!this.addEvent(e)) return;							// add event to unfolding
				
				Event corr = this.checkCutoffA(e);						// check for cutoff event
				if (corr!=null) this.addCutoff(e,corr);					// e is cutoff event
				
				// The following functionality is not captured by Esparza's algorithm !!!
				// The code handles situation when there exist a cutoff event which induces initial marking
				// The identification of such cutoff was postponed to the point until second event which induces initial marking is identified
				//if (corrIni == null) {
					//boolean isCutoffIni = e.getLocalConfiguration().getMarking().equals(this.net.getMarking());
					//if (cutoffIni == null && isCutoffIni) cutoffIni = e;
					//else if (cutoffIni != null && corrIni == null && isCutoffIni) {
						//corrIni = e;
						//this.cutoff2corr.put(cutoffIni, corrIni);
					//}
				//}
				
				pe = getPossibleExtensionsA();							// get possible extensions of branching process
			}
			else {
				pe.remove(e);	
			}
		}
	}*/
    protected IPossibleExtensions<BPN, C, E, F, N, P, T, M> getInitialPossibleExtensions() {
        IPossibleExtensions<BPN, C, E, F, N, P, T, M> result = new AbstractPossibleExtensions<BPN, C, E, F, N, P, T, M>(this.ADEQUATE_ORDER);

        for (T t : this.sys.getTransitions()) {
            ICoSet<BPN, C, E, F, N, P, T, M> coset = this.containsPlaces(this.getInitialCut(), this.sys.getPreset(t));

            if (coset != null) { // if there exists such a co-set
                result.add(this.createEvent(t, coset));
            }
        }

        return result;
    }

    private Set<E> updatePossibleExtensions(E e) {
        this.UPE = new HashSet<E>();

        T u = e.getTransition();
        Set<T> upp = new HashSet<T>(this.sys.getPostsetTransitions(this.sys.getPostset(u)));
        Set<P> pu = new HashSet<P>(this.sys.getPreset(u));
        pu.removeAll(this.sys.getPostset(u));
        upp.removeAll(this.sys.getPostsetTransitions(pu));

        for (T t : upp) {
            ICoSet<BPN, C, E, F, N, P, T, M> preset = this.createCoSet();
            for (C b : e.getPostConditions()) {
                if (this.sys.getPreset(t).contains(b.getPlace()))
                    preset.add(b);
            }
            Set<C> C = this.getConcurrentConditions(e);
            this.cover(C, t, preset);
        }
     
        return this.UPE;
    }

    @SuppressWarnings("unchecked")
    private void cover(Set<C> CC, T t, ICoSet<BPN, C, E, F, N, P, T, M> preset) {
        if (this.sys.getPreset(t).size() == preset.size()) {
        	this.UPE.add(this.createEvent(t, preset));
        } else {
            Set<P> pre = new HashSet<P>(this.sys.getPreset(t));
            pre.removeAll(this.getPlaces(preset));
            P p = pre.iterator().next();

            for (C d : CC) {
                // add "!d.isCutoffPost()"
                // by Shudi Wang
                //if (!d.isCutoffPost() && d.getPlace().equals(p)) {
    				if (d.getPlace().equals(p)) {
                    Set<C> C2 = new HashSet<C>();
                    for (C dd : CC)
                        if (this.areConcurrent((BPN) d, (BPN) dd))
                            C2.add(dd);
                    ICoSet<BPN, C, E, F, N, P, T, M> preset2 = this.createCoSet();
                    preset2.addAll(preset);
                    preset2.add(d);
                    this.cover(C2, t, preset2);
                }
            }
        }
    }

    private Set<P> getPlaces(ICoSet<BPN, C, E, F, N, P, T, M> coset) {
        Set<P> result = new HashSet<P>();

        for (C c : coset)
            result.add(c.getPlace());

        return result;
    }

    @SuppressWarnings("unchecked")
    private Set<C> getConcurrentConditions(E e) {
        Set<C> result = new HashSet<C>();

        for (C c : this.getConditions()) {
            if (this.areConcurrent((BPN) e, (BPN) c))
                result.add(c);
        }

        return result;
    }

    protected ICoSet<BPN, C, E, F, N, P, T, M> containsPlaces(ICoSet<BPN, C, E, F, N, P, T, M> coset, Collection<P> places) {
        ICoSet<BPN, C, E, F, N, P, T, M> result = this.createCoSet();

        for (P p : places) {
            boolean flag = false;
            for (C c : coset) {
                if (c.getPlace().equals(p)) {
                    flag = true;
                    result.add(c);
                    break;
                }
            }
            if (!flag) return null;
        }

        return result;
    }

    protected E checkCutoffA(E cutoff) {
        ILocalConfiguration<BPN, C, E, F, N, P, T, M> lce = cutoff.getLocalConfiguration();
        
        for (E f : this.getEvents()) {
            if (f.equals(cutoff)) continue;
            ILocalConfiguration<BPN, C, E, F, N, P, T, M> lcf = f.getLocalConfiguration();
            if (lce.getMarking().equals(lcf.getMarking()) && this.ADEQUATE_ORDER.isSmaller(lcf, lce)) {
            	return f;
            	        //          return this.checkCutoffB(cutoff, f); // check cutoff extended conditions            		
            }
        }

        return null;
    }

    protected E checkCutoffB(E cutoff, E corr) {
        return corr;
    }

    protected void addCutoff(E e, E corr) {
        this.cutoff2corr.put(e, corr);
        // add by Shudi Wang 15/05/26 to create mapping conditions
        /*
        while (this.cutoff2corr.containsKey(corr)) {
            corr = this.cutoff2corr.get(corr);
        }
        for (C newC : e.getPostConditions()) {
            newC.setCutoffPost(true);
            for (C oldC : corr.getPostConditions()) {
                if (oldC.getPlace() == newC.getPlace()) {
                    if (oldC.getMappingConditions() == null) {
                        oldC.setMappingConditions(new HashSet<C>());
                        oldC.getMappingConditions().add(oldC);
                    }
                    oldC.getMappingConditions().add(newC);
                    newC.setMappingConditions(oldC.getMappingConditions());
                    newC.setCorrespondingCondition(oldC);
                }
            }
        }*/
    }

    @Override
    public Set<E> getCutoffEvents() {
        return this.cutoff2corr.keySet();
    }

    @Override
    public boolean isCutoffEvent(E event) {
        return this.cutoff2corr.containsKey(event);
    }

    @Override
    public E getCorrespondingEvent(E event) {
        return this.cutoff2corr.get(event);
    }

    @Override
    public List<T> getTotalOrderOfTransitions() {
        return this.totalOrderTs;
    }

    @Override
    public IOccurrenceNet<BPN, C, E, F, N, P, T, M> getOccurrenceNet() {
        try {
            @SuppressWarnings("unchecked")
            IOccurrenceNet<BPN, C, E, F, N, P, T, M> occ = (IOccurrenceNet<BPN, C, E, F, N, P, T, M>) OccurrenceNet.class.newInstance();
            occ.setCompletePrefixUnfolding(this);
            return occ;
        } catch (InstantiationException e) {
            e.printStackTrace();
            return null;
        } catch (IllegalAccessException e) {
            e.printStackTrace();
            return null;
        }
    }
	
	/*protected Set<Event> getPossibleExtensionsA() {
		Set<Event> result = new HashSet<Event>();
		
		// iterate over all transitions of the originative net
		for (Transition t : this.sys.getTransitions()) {
			// iterate over all places in the preset
			Collection<Place> pre = this.sys.getPreset(t);
			Place p = pre.iterator().next();
			// get cuts that contain conditions that correspond to the place
			Collection<Cut> cuts = this.getCutsWithPlace(p);
			// iterate over cuts
			for (Cut cut : cuts) {
				// get co-set of conditions that correspond to places in the preset (contained in the cut)
				CoSet coset = this.containsPlaces(cut,pre);
				if (coset!=null) { // if there exists such a co-set
					// check if there already exists an event that corresponds to the transition with the preset of conditions which equals to coset 
					boolean flag = false;
					if (t2es.get(t)!=null) {
						for (IEvent e : t2es.get(t)) {
							//if (this.areEqual(e.getPreConditions(),coset)) {
							if (coset.equals(e.getPreConditions())) {
								flag = true;
								break;
							}
						}
					}
					if (!flag) { // we found possible extension !!!
						Event e = new Event(this,t,coset);
						result.add(e);
					}
				}
			}
		}
		
		result.addAll(this.getPossibleExtensionsB(result));
		
		return result;
	}*/
	
	/*protected Set<Event> getPossibleExtensionsB(Set<Event> pe) {
		return new HashSet<Event>();
	}*/	
	
	/*private void updateConcurrency(Cut cut) {
		for (Condition c1 : cut) {
			if (this.co.get(c1)==null) this.co.put(c1, new HashSet<BPNode>());
			Event e1 = c1.getPreEvent();
			if (e1 != null && this.co.get(e1)==null) this.co.put(e1, new HashSet<BPNode>());
			for (Condition c2 : cut) {
				if (this.co.get(c2)==null) this.co.put(c2, new HashSet<BPNode>());
				this.co.get(c1).add(c2);
				
				Event e2 = c2.getPreEvent();
				if (e1!=null && e2!=null && !this.ca.get(e1).contains(e2) && !this.ca.get(e2).contains(e1)) this.co.get(e1).add(e2);
				if (!c1.equals(c2) && e1!=null && !this.ca.get(c2).contains(e1) && !this.ca.get(e1).contains(c2)) {
					this.co.get(c2).add(e1);
					this.co.get(e1).add(c2);
				}
			}
		}
	}*/
	
	

	/*protected Set<Cut> getCutsWithPlace(Place p) {
		Set<Cut> result = new HashSet<Cut>();
		
		Collection<Condition> cs = p2cs.get(p);
		if (cs==null) return result;
		for (ICondition c : cs) {
			Collection<Cut> cuts = c2cut.get(c);
			if (cuts!=null) result.addAll(cuts);	
		}
		
		return result;
	}*/
	
	/*protected boolean contains(Collection<Condition> cs1, Collection<Condition> cs2) {
		for (ICondition c1 : cs2) {
			boolean flag = false;
			for (ICondition c2 : cs1) {
				if (c1.equals(c2)) {
					flag = true;
					break;
				}
			}
			if (!flag) return false;
		}
		
		return true;
	}*/

	/*protected boolean addCut(ICut<N,P,T,C,E> cut) {
		this.updateConcurrency(cut);
		
		Map<Place,Integer> p2i = new HashMap<Place,Integer>();
		
		for (Condition c : cut) {
			// check bound
			Integer i = p2i.get(c.getPlace());
			if (i==null) p2i.put(c.getPlace(),1);
			else {
				if (i == this.setup.MAX_BOUND) return false;
				else p2i.put(c.getPlace(),i+1);
			}
			
			if (c2cut.get(c)!=null) c2cut.get(c).add(cut);
			else {
				Collection<Cut> cuts = new ArrayList<Cut>();
				cuts.add(cut);
				c2cut.put(c,cuts);
			}
		}
		
		return true;
	}*/
	
	/*@Override
	public CompletePrefixUnfoldingSetup getSetup() {
		return this.setup;
	}*/
	 
	
	 
	
	

	
	 
	/*@Override
	public OrderingRelationType getOrderingRelation(BPNode n1, BPNode n2) {
		if (this.areCausal(n1,n2)) return OrderingRelationType.CAUSAL;
		if (this.areInverseCausal(n1,n2)) return OrderingRelationType.INVERSE_CAUSAL;
		if (this.areInConflict(n1,n2)) return OrderingRelationType.CONFLICT;
		return OrderingRelationType.CONCURRENT;
	}*/
	 
	/*@Override
	public IOccurrenceNet getOccurrenceNet() {
		this.occNet = new OccurrenceNet(this); 
		return this.occNet; 
	}*/
	
	/*public void printOrderingRelations() {
		List<BPNode> ns = new ArrayList<BPNode>();
		ns.addAll(this.getConditions());
		ns.addAll(this.getEvents());
		
		System.out.println(" \t");
		for (BPNode n : ns) System.out.print("\t"+n.getName());
		System.out.println();
		
		for (BPNode n1 : ns) {
			System.out.print(n1.getName()+"\t");
			for (BPNode n2 : ns) {
				String rel = "";
				if (this.areCausal(n1,n2)) rel = ">";
				if (this.areInverseCausal(n1,n2)) rel = "<";
				if (this.areConcurrent(n1,n2)) rel = "@";
				if (this.areInConflict(n1,n2)) rel = "#";
				System.out.print(rel + "\t");
			}
			System.out.println();
		}
	}*/
	 
	/*@Override
	public Set<Event> getCutoffEvents() {
		return this.cutoff2corr.keySet();
	}*/
	 
	/*@Override
	public boolean isCutoffEvent(IEvent e) {
		return this.cutoff2corr.containsKey(e);
	}*/
	 
	/*@Override
	public IEvent getCorrespondingEvent(IEvent e) {
		return this.cutoff2corr.get(e);
	}*/

	/*@Override
	public Set<C> getConditions(P place) {
		// TODO Auto-generated method stub
		return null;
	}*/

	/*@Override
	public Set<E> getEvents(T transition) {
		// TODO Auto-generated method stub
		return null;
	}*/

    @SuppressWarnings("unchecked")
    @Override
    public E createEvent(T transition, ICoSet<BPN, C, E, F, N, P, T, M> preConditions) {
        E e = null;
        try {
            e = (E) Event.class.newInstance();
            e.setTransition(transition);
            e.setPreConditions(preConditions);
            e.setCompletePrefixUnfolding(this);
            // Add by Shudi Wang 15/05/26
            for (C c : preConditions) {
                c.getPostE().add(e);
            }
            return e;
        } catch (InstantiationException exception) {
            exception.printStackTrace();
            return e;
        } catch (IllegalAccessException exception) {
            exception.printStackTrace();
            return e;
        }
    }

    @Override
    public boolean isHealthyCutoffEvent(E event) {
        E corr = this.getCorrespondingEvent(event);
        if (corr == null) return false;

        Set<C> ecs = new HashSet<C>(event.getLocalConfiguration().getCut());
        Set<C> ccs = new HashSet<C>(corr.getLocalConfiguration().getCut());

        ecs.removeAll(event.getPostConditions());
        ccs.removeAll(corr.getPostConditions());

        if (ecs.equals(ccs))
            return true;

        return false;
    }

    @Override
    public boolean isProper() {
        for (E e : this.getEvents()) {
            E corr = this.getCorrespondingEvent(e);
            if (corr == null) continue;

            if (!this.isHealthyCutoffEvent(e))
                return false;
        }
        return true;
    }
}
