theory HAMRMicro05Spec
  imports HAMRMicro05ExecutionSemantics
begin

subsection \<open>General Helper Functions\<close>

text \<open>Get the task ID for the task/transition fired by a set of RIDs\<close>

definition getTid :: "Rids \<Rightarrow> 'value System \<Rightarrow> Tid"
  where "getTid rids sys = (activationMap sys) $ rids"

text \<open>Get the action of a task given it's ID\<close>

definition getAction :: "'value System \<Rightarrow> Tid \<Rightarrow> 'value Action"
  where "getAction sys tid = action ((taskMap sys) $ tid)"

text \<open>Get a tuple containing the task state for a task and the global channel state given the
      task's ID and the system state\<close>

definition getTaskChannelState :: "'value System \<Rightarrow> Tid \<Rightarrow> 'value SystemState \<Rightarrow> ('value TaskState \<times> 'value ChState)"
  where "getTaskChannelState sys tid st = (((systemTasks st) $ tid), (systemChs st))"

text \<open>Get a tuple containing the task state for a task and the global channel state given the
      task's ID and a tuple containing all task states and the global channel state\<close>

definition getTaskChannelStateAlt :: "'value System \<Rightarrow> Tid \<Rightarrow> ((Tid, 'value TaskState) map \<times> 'value ChState) \<Rightarrow> ('value TaskState \<times> 'value ChState)"
  where "getTaskChannelStateAlt sys tid ttscs = (((fst ttscs) $ tid), (snd ttscs))"

text \<open>Apply a task's action to the current system state and return the updated task state and global
      channel state\<close>

definition applyAction :: "'value System \<Rightarrow> Tid \<Rightarrow> 'value SystemState \<Rightarrow> ('value TaskState \<times> 'value ChState)"
  where "applyAction sys tid st = (getAction sys tid) (getTaskChannelState sys tid st)"

text \<open>Apply a task's action to the current global channel state and all task states and return the 
      updated task state and global channel state\<close>

definition applyActionAlt :: "'value System \<Rightarrow> Tid \<Rightarrow> ((Tid, 'value TaskState) map \<times> 'value ChState) \<Rightarrow> ('value TaskState \<times> 'value ChState)"
  where "applyActionAlt sys tid ttscs = (getAction sys tid) (getTaskChannelStateAlt sys tid ttscs)"

text \<open>Apply a task's action to the current system state and return the updated set of task states 
      and the global channel state\<close>

definition applyActionGlobal :: "'value System \<Rightarrow> Tid \<Rightarrow> 'value SystemState \<Rightarrow> ((Tid, 'value TaskState) map \<times> 'value ChState)"
  where "applyActionGlobal sys tid st =
                  (((systemTasks st) (tid \<mapsto> (fst (applyAction sys tid st)))) 
                  , (snd (applyAction sys tid st)))"

text \<open>Apply a task's action to the current global channel state and all task states and return the 
      updated set of task states and the global channel state\<close>

definition applyActionGlobalAlt :: "'value System \<Rightarrow> Tid \<Rightarrow> ((Tid, 'value TaskState) map \<times> 'value ChState) \<Rightarrow> ((Tid, 'value TaskState) map \<times> 'value ChState)"
  where "applyActionGlobalAlt sys tid ttscs =
                  (((fst ttscs) (tid \<mapsto> fst (applyActionAlt sys tid ttscs))) 
                  , (snd (applyActionAlt sys tid ttscs)))"

text \<open>Compose two task actions and apply them to the current state\<close>

definition applyActionGlobalComp :: "'value System \<Rightarrow> Tid \<Rightarrow> Tid \<Rightarrow> 'value SystemState \<Rightarrow> ((Tid, 'value TaskState) map \<times> 'value ChState)"
  where "applyActionGlobalComp sys tid1 tid2 st \<equiv> applyActionGlobalAlt sys tid2 (applyActionGlobal sys tid1 st)"

subsection \<open>Specification category: Task Specifications\<close>

text \<open>Each task (each task action, specifically), has a pre and post-condition. 
 
The precondition is a constraint on the pre-state Task State and Channel State. 
There will be verification obligations to show that for all
tasks, every system assertion that holds before the task implies
the precondition.
 
The post-condition is a transfer relation between the pre- and 
post-state Task States and Channel States.  The verification obligations for the post-conditions
are to ensure that the task action satisfies the post-condition relation
under the assumption that the precondition holds.\<close>

type_synonym 'value TaskPre = "'value TaskState \<Rightarrow> 'value ChState \<Rightarrow> bool"
type_synonym 'value TaskPost = "'value TaskState \<Rightarrow> 'value ChState \<Rightarrow> 'value TaskState \<Rightarrow> 'value ChState \<Rightarrow> bool"

text \<open>The following structure holds all the user contracts for system.  
Isabelle maps are used to associate each task identifier with a 
pre- and post- condition.\<close>

record 'value TaskContracts =
  taskPre :: "(Tid, 'value TaskPre) map"
  taskPost :: "(Tid, 'value TaskPost) map"

fun mkTaskContracts :: "(Tid, 'value TaskPre) map \<Rightarrow> (Tid, 'value TaskPost) map \<Rightarrow> 'value TaskContracts"
  where "mkTaskContracts preMap postMap  = 
           \<lparr>taskPre = preMap, taskPost = postMap\<rparr>"

text \<open>A task contract is well-formed if the preconditions only refer to the in channels for the task\<close>

definition wf_TaskContracts_ChState_Pre :: "'value System \<Rightarrow> Model \<Rightarrow> 'value TaskContracts \<Rightarrow> bool"
  where "wf_TaskContracts_ChState_Pre sys m tc \<equiv>
          \<comment> \<open>for all task\<close>
          \<forall>tid \<in> (dom (taskMap sys)). 
              \<comment> \<open>for any two states\<close>
              \<forall>(st1 :: 'value SystemState) (st2 :: 'value SystemState).
                \<comment> \<open>if for all in-channels, st1 and st2 are equal\<close>
                (\<forall>c \<in> (inChIds ((modelTaskDescrs m) $ tid)). (systemChs st1) $ c = (systemChs st2) $ c) 
                \<longrightarrow> 
                \<comment> \<open>then the precondition should be true for st1 iff it is for st2\<close>
                ((taskPre tc) $ tid) (fst (getTaskChannelState sys tid st1)) (snd (getTaskChannelState sys tid st1)) 
                = ((taskPre tc) $ tid) (fst (getTaskChannelState sys tid st2)) (snd (getTaskChannelState sys tid st2))"

text \<open>A task contract is well-formed if the post conditions only refer to the input channels of st1
      and st2 and the out-channels st1' and st2'\<close>

(* Observing a input port in the post state in the post condition  doesn't matter because, due to the
   well-formedness of the action, the input ports are not affected by the action so they can be
   be replace with the same statement but referring to the pre-state by Isabelle*)

definition wf_TaskContracts_ChState_Post :: "'value System \<Rightarrow> Model \<Rightarrow> 'value TaskContracts \<Rightarrow> bool"
  where "wf_TaskContracts_ChState_Post sys m tc \<equiv>
          \<comment> \<open>for all task\<close>
          \<forall>tid \<in> (dom (taskMap sys)). 
              \<comment> \<open>for any two states\<close>
              \<forall>(st1 :: 'value SystemState) (st2 :: 'value SystemState).
                \<comment> \<open>if st1 and st2  have the same input channels and the two resulting states st1'
                    and st2' have the same values in the out channels\<close>
                (\<forall>c \<in> (inChIds ((modelTaskDescrs m) $ tid)). 
                  \<forall>c' \<in> (outChIds ((modelTaskDescrs m) $ tid)). 
                    (systemChs st1) $ c = (systemChs st2) $ c 
                    \<and> (snd (applyAction sys tid st1)) $ c' = (snd (applyAction sys tid st2)) $ c')
                    \<longrightarrow>
                    \<comment> \<open>then the task post condition is only true for st1 and st1' iff it is true for
                        st2 and st2'\<close>
                    (((taskPost tc) $ tid) (fst (getTaskChannelState sys tid st1)) (snd (getTaskChannelState sys tid st1))
                                          (fst (applyAction sys tid st1)) (snd (applyAction sys tid st1))
                    = ((taskPost tc) $ tid) (fst (getTaskChannelState sys tid st2)) (snd (getTaskChannelState sys tid st2))
                                          (fst (applyAction sys tid st2)) (snd (applyAction sys tid st2)))"


text \<open>A TaskContracts structure is well-formed if all task transitions have a pre and post condition
      and all other WF conditions hold\<close>

definition wf_TaskContracts :: "'store System \<Rightarrow> Model \<Rightarrow> 'store TaskContracts \<Rightarrow> bool"
  where "wf_TaskContracts sys m tcs \<equiv> ((systemTids sys) = dom (taskPre tcs)
                                   \<and> (systemTids sys) = dom (taskPost tcs))
                                   \<and> wf_TaskContracts_ChState_Pre sys m tcs
                                   \<and> wf_TaskContracts_ChState_Post sys m tcs"

subsection \<open>Specification category: System Specifications\<close>


text \<open>System Assertions are a constraint on the global task and channel state of the system
      at certain points in the schedule that are relative to the execution of some task. There
      will be verification conditions to show that, for every transition in the petri net, all assertions
      that are true in the input places should imply all assertions at the ouptut places and, given
      the transition is tied to a task, the precondition of the task. These properties are the
      composition/integration properties: the outputs of any components that can precede the current
      component must imply the precondition of the current component and any assertion that can
      be made following it.

      The pre-assertions of a transition refer to all assertions tied to the in places of the transitions
      The post-assertions of a transition refer to all assertions tied to the out places of the transitions\<close>

type_synonym 'value SystemAssert = "(Tid, 'value TaskState) map \<Rightarrow> 'value ChState \<Rightarrow> bool"

text \<open>This record is used to map system assertions to places/RIDs in the Petri net.\<close>

record 'value SystemSpec = 
  sysPlaceAsserts :: "(Rid, 'value SystemAssert) map"

definition mkSysSpec :: "(Rid, 'value SystemAssert) map \<Rightarrow> 'value SystemSpec"
  where "mkSysSpec spa \<equiv> \<lparr>sysPlaceAsserts = spa\<rparr>"

text \<open>A System Spec is well-formed given that every places in the Petri net has an assertion\<close>
definition wf_SystemSpec :: "'value SystemSpec \<Rightarrow> 'value System \<Rightarrow> bool"
  where "wf_SystemSpec sysSpec sys \<equiv> dom (sysPlaceAsserts sysSpec) = systemNextRelRids sys"

subsection \<open>More helper functions\<close>

text \<open>Conjoin all assertions tied to all input places for a transition\<close>

definition ballAssert :: "'value SystemSpec \<Rightarrow> 'value SystemState \<Rightarrow> Rids \<Rightarrow> bool"
  where "ballAssert sysSpec st inRids = 
         Ball {((sysPlaceAsserts sysSpec) $ r) (systemTasks st) (systemChs st) | r. r \<in> fset inRids} (\<lambda>x. x)"

definition ballAssertAlt :: "'value SystemSpec \<Rightarrow> ((Tid, 'value TaskState) map \<times> 'value ChState) \<Rightarrow> Rids \<Rightarrow> bool"
  where "ballAssertAlt sysSpec ttscs inRids = 
         Ball {((sysPlaceAsserts sysSpec) $ r) (fst ttscs) (snd ttscs) | r. r \<in> fset inRids} (\<lambda>x. x)"

text \<open>if all asserts in s1 hold for the state and all asserts in s2 hold for the state, then 
      all asserts in s1 |\<union>| s2 hold for st\<close>
lemma ballAssertUnion: "\<forall>s1 s2 st. 
                            ballAssert sysSpec st s1 
                            \<and> ballAssert sysSpec st s2 
                            \<longrightarrow> 
                            ballAssert sysSpec st (s1 |\<union>| s2)"
    by (smt (verit, ccfv_SIG) ballAssert_def funion_iff mem_Collect_eq)

text \<open>Get the set of all transitions in the Petri net as a set of tuples of a transitions input
      and out put places\<close>

definition getAllTransition :: "'value System \<Rightarrow> (Rids \<times>  Rids) set"
  where "getAllTransition sys \<equiv> {(inRids, outRids) | inRids outRids. inRids \<in> (dom (nextRel sys)) \<and> outRids = (nextRel sys) $ inRids}"

text \<open>Get all in places that precede a transition\<close>

definition getPrecedingPlaces :: "(Rids \<times>  Rids) \<Rightarrow> Rids"
  where "getPrecedingPlaces ridsRel \<equiv> fst ridsRel"

text \<open>Get all out places that follow a transition\<close>

definition getFollowingPlaces :: "(Rids \<times>  Rids) \<Rightarrow> Rids"
  where "getFollowingPlaces ridsRel \<equiv> snd ridsRel"

subsection \<open>Property category: May Happen In Parallel\<close>

(* Could be generated by a domination/control dependence analysis over Petri net*)

text \<open>MHIP Relation is a set of pairs of transition that may happen in parallel. All transitions
      are labeled by there in places\<close>
type_synonym MayHappenInParallelRel = "(Rids \<times> Rids) set"

text \<open>A MHIP relation is well-formed if all pairs of RIDs in the set are pairs of transitions\<close>
definition wf_MayHappenInParallelRel_dom ::  "'value System \<Rightarrow> MayHappenInParallelRel \<Rightarrow> bool"
  where "wf_MayHappenInParallelRel_dom sys mhip \<equiv> 
          \<forall>rel \<in> mhip. (fst rel) \<in> (dom (nextRel sys)) \<and> (snd rel) \<in> (dom (nextRel sys)) \<and> (fst rel) \<noteq> (snd rel)"

text \<open>Two distinct transition F and S are in the MHIP relation if and only if there exist a reachable
      state where both transitions are fireable\<close>
definition MHIP_assumption :: "MayHappenInParallelRel \<Rightarrow> 'value System \<Rightarrow> Model \<Rightarrow> bool"
  where "MHIP_assumption mhip sys m \<equiv> \<forall>f s. f \<in> dom(nextRel sys) \<and> s \<in> dom(nextRel sys) \<and> f \<noteq> s \<longrightarrow>
          (f, s) \<in> mhip 
          \<longleftrightarrow> 
          (\<exists>schst. scheduleReachBody (nextRel sys) {|modelStartRid m|} schst \<and> f |\<subseteq>| schst \<and> s |\<subseteq>| schst)"

text \<open>It is possible to reach a schedule state containing F and S if it is possible to reach a schedule
      state that contains the in places of F, the out places of S, and the out places of S are a subset
      of the in places of some JOIN\<close>
definition BackStepReachability_Assumption :: "'value System \<Rightarrow> Model \<Rightarrow> bool"
  where "BackStepReachability_Assumption sys m \<equiv> 
          \<forall>f s. f \<in> dom(nextRel sys) 
                \<and> s \<in> dom(nextRel sys) 
                \<and> f \<noteq> s 
                \<comment> \<open>if (nextRel sys $ s) is at the end of a parallel path (join)\<close>
                \<and> (\<exists>d \<in> dom(nextRel sys). fcard(d) > 1 \<and> (nextRel sys $ s) |\<subseteq>| d \<and> f \<noteq> d \<and> s \<noteq> d)  
                \<longrightarrow>
                (\<exists>schst. scheduleReachBody (nextRel sys) {|modelStartRid m|} schst \<and> f |\<subseteq>| schst \<and> (nextRel sys $ s) |\<subseteq>| schst) 
                \<longrightarrow> 
                (\<exists>schst. scheduleReachBody (nextRel sys) {|modelStartRid m|} schst \<and> f |\<subseteq>| schst \<and> s |\<subseteq>| schst)
            "

subsection \<open>Property category: Execution Independence\<close>

text \<open>Two component transition, c1 and c2, (defined by their input places/input RIDs) are executionally 
      independent of each other if, given a state, st, that satisfies both transitions' pre-assertions,
      executing c1 then c2 on st results in the same system state as executing c2 then c1 on st.
      
      If one or both of the transitions is a control point transition then the two transitions are
      trivially independent.\<close>

definition execIndependent :: "'value System \<Rightarrow> 'value SystemSpec \<Rightarrow> Rids \<Rightarrow> Rids \<Rightarrow> bool"
  where "execIndependent sys sysSpec rids1 rids2 \<equiv> 
    (rids1 \<in> (dom (activationMap sys)) \<and> rids2 \<in> (dom (activationMap sys))) \<longrightarrow>
    (\<forall>st. (ballAssert sysSpec st rids1 \<and> ballAssert sysSpec st rids2) 
          \<longrightarrow> 
          (applyActionGlobalComp sys (getTid rids1 sys) (getTid rids2 sys) st 
          = applyActionGlobalComp sys (getTid rids2 sys) (getTid rids1 sys) st))"

subsection \<open>Property category: nonBlocking\<close>

text \<open>Two transitions, t1 and t2, (defined by their input places/input RIDs) are non-blocking if, 
      given a state, st, that satisfies both transitions' pre-assertions, firing t1 on st should
      produce a state that satisfies the pre-assertions of t2 and vice versa.

      If both transitions are control point transitions then they are trivially non blocking \<close>

definition nonBlocking :: "'value System \<Rightarrow> 'value SystemSpec \<Rightarrow> Rids \<Rightarrow> Rids \<Rightarrow> bool"
  where "nonBlocking sys sysSpec rids1 rids2 \<equiv> 
      rids1 \<in> (dom (activationMap sys)) \<or> rids2 \<in> (dom (activationMap sys)) \<longrightarrow>
      (\<forall>st. 
        (
          (ballAssert sysSpec st rids1
          \<and> ballAssert sysSpec st rids2
          \<and> rids1 \<in> (dom (activationMap sys)))
          \<longrightarrow> ballAssertAlt sysSpec (applyActionGlobal sys (getTid rids1 sys) st) rids2
        )
        \<and>
        (
          ( ballAssert sysSpec st rids1
          \<and> ballAssert sysSpec st rids2
          \<and> rids2 \<in> (dom (activationMap sys)))
          \<longrightarrow> ballAssertAlt sysSpec (applyActionGlobal sys (getTid rids2 sys) st) rids1
        )
      )
"

text \<open>Two transitions, t1 and t2, do not contradict the others post assertions if, given a state, st,
      that satisfies the pre-assertions of t1 and the post-assertions of t2, firing t1 should not
      contradict the post-assertions of t2 and vice versa

      If both transitions are control point transitions then they trivially do not contradict the
      post assertions of the other transition\<close>
definition nonContradictPost :: "'value System \<Rightarrow> 'value SystemSpec \<Rightarrow> Rids \<Rightarrow> Rids \<Rightarrow> bool"
  where "nonContradictPost sys sysSpec rids1 rids2 \<equiv> 
      rids1 \<in> (dom (activationMap sys)) \<or> rids2 \<in> (dom (activationMap sys)) \<longrightarrow>
      (\<forall>st. 
        (
          (ballAssert sysSpec st rids1
          \<and> ballAssert sysSpec st (nextRel sys $ rids2)
          \<and> rids1 \<in> (dom (activationMap sys)))
          \<longrightarrow> ballAssertAlt sysSpec (applyActionGlobal sys (getTid rids1 sys) st) (nextRel sys $ rids2)
        )
        \<and>
        (
          ( ballAssert sysSpec st (nextRel sys $ rids1)
          \<and> ballAssert sysSpec st rids2
          \<and> rids2 \<in> (dom (activationMap sys)))
          \<longrightarrow> ballAssertAlt sysSpec (applyActionGlobal sys (getTid rids2 sys) st) (nextRel sys $ rids1)
        )
      )
"

subsection \<open>Property category: Total Independence\<close>

text \<open>If two transitions are both non-blocking and executionally independent, then they are independent.\<close>

definition independent :: "'value System \<Rightarrow> 'value SystemSpec \<Rightarrow> Rids \<Rightarrow> Rids \<Rightarrow> bool"
  where "independent sys sysSpec rids1 rids2 \<equiv> execIndependent sys sysSpec rids1 rids2 
                                               \<and> nonBlocking sys sysSpec rids1 rids2
                                               \<and> nonContradictPost sys sysSpec rids1 rids2"

text \<open>All transitions that may happen in parallel must be independent.\<close>

definition mayHappenInParallelInd :: "MayHappenInParallelRel \<Rightarrow> 'value System \<Rightarrow> 'value SystemSpec \<Rightarrow> bool"
  where "mayHappenInParallelInd mhip sys sysSpec \<equiv> \<forall>rel \<in> mhip. independent sys sysSpec (fst rel) (snd rel)"

subsection \<open>Property Category: Modifies Clause\<close>

text \<open>
We do not put restrictions on what the frame refer to due to the well-formedness restrictions
put on the actions and task and what they can refer to. If we do refer to something that
does not belong to the task then it is either trivial, a consequence of the wf-conditions, or
not directly provable.

The proof of correctness is trivial if it only refers to equalities (which is not enforced) and is
meant to act as an auxilary proof so that the system level proofs do not have to refer to the action
of a task transition
\<close>

text \<open>Given a pre-state and a post-state, define which local variables and channels are unchanged\<close>
type_synonym 'value LocalFrame = "('value TaskState \<times> 'value ChState) \<Rightarrow> ('value TaskState \<times> 'value ChState) \<Rightarrow> bool"

text \<open>Given a pre-state and a post-state, define which task states and channels are unchanged\<close>
type_synonym 'value GlobalFrame = "((Tid \<Rightarrow> 'value TaskState option) \<times> 'value ChState) \<Rightarrow> ((Tid \<Rightarrow> 'value TaskState option) \<times> 'value ChState) \<Rightarrow> bool"

record 'value WriteFrame =
  lFrame :: "(Tid, 'value LocalFrame) map"
  gFrame :: "(Tid, 'value GlobalFrame) map"

text \<open>All tasks specified in the model should have a local write frame and global write frame\<close>
definition wf_WriteFrame_Dom :: "'value System \<Rightarrow> Model \<Rightarrow> 'value WriteFrame \<Rightarrow> bool"
  where "wf_WriteFrame_Dom sys m wrf \<equiv> (modelTids m) = dom (lFrame wrf) 
                                        \<and> (modelTids m) = dom (gFrame wrf)"

text \<open>For all tasks, the action should satisfy the local write frame under execution for all states\<close>
definition wf_WriteFrame_LocalExec :: "'value System \<Rightarrow> Model \<Rightarrow> 'value WriteFrame \<Rightarrow> bool"
  where "wf_WriteFrame_LocalExec sys m wrf \<equiv> 
          \<forall>t \<in> dom(lFrame wrf). 
            \<forall>st.                                 
              ((lFrame wrf) $ t) (getTaskChannelState sys t st) (applyAction sys t st)"

text \<open>For all tasks, the action should satisfy the global write frame under execution for all states\<close>
definition wf_WriteFrame_GlobalExec :: "'value System \<Rightarrow> Model \<Rightarrow> 'value WriteFrame \<Rightarrow> bool"
  where "wf_WriteFrame_GlobalExec sys m wrf \<equiv> 
          \<forall>t \<in> dom(gFrame wrf). 
              \<forall>st.
                ((gFrame wrf) $ t) (systemTasks st, systemChs st) (applyActionGlobal sys t st)"

                                                                                   
definition wf_WriteFrame :: "'value System \<Rightarrow> Model \<Rightarrow> 'value WriteFrame \<Rightarrow> bool"
  where "wf_WriteFrame sys m wrf \<equiv> 
          wf_WriteFrame_Dom sys m wrf
          \<and> wf_WriteFrame_LocalExec sys m wrf
          \<and> wf_WriteFrame_GlobalExec sys m wrf"
  
named_theorems wf_WriteFrame_simps
lemmas [wf_WriteFrame_simps] =
  wf_WriteFrame_def
  wf_WriteFrame_Dom_def
  wf_WriteFrame_LocalExec_def
  wf_WriteFrame_GlobalExec_def    

(* -------- S c h e d u l e   C o n t r a c t    V C s --------------*)

(* NEED TO DO WF CONDITIONS FOR SYSTEM STATE*)

(* -------- T a s k         C o n t r a c t                V C s --------------*)

text \<open>If a transition is a component transition, then, given a state that satisfies the precondition,
      the state resulting from applying the action should satisfy the post condition\<close>

definition applyPrePost :: "'value System \<Rightarrow> 'value TaskContracts \<Rightarrow> Tid 
                                          \<Rightarrow> 'value TaskState \<times> 'value ChState
                                          \<Rightarrow> 'value TaskState \<times> 'value ChState 
                                          \<Rightarrow> bool"
  where "applyPrePost sys tc tid tscs tscs' \<equiv> 
                                        \<comment> \<open>if the pre-state satisfies the precondition\<close>
                                        ((taskPre tc) $ tid) (fst tscs) (snd tscs) 
                                        \<longrightarrow>
                                        \<comment> \<open>then the pre-state and the post-state resulting from the
                                            applying the action should satisfy the post-condition\<close>
                                        ((taskPost tc) $ tid) (fst tscs) (snd tscs) (fst tscs') (snd tscs')"

definition taskConVC :: "'value System \<Rightarrow> Model \<Rightarrow> 'value TaskContracts \<Rightarrow> Rids \<Rightarrow> bool"
  where "taskConVC sys m tc rids \<equiv>
          rids \<in> (dom (activationMap sys)) \<longrightarrow>
          (\<forall> (st :: 'value SystemState). 
              (applyPrePost sys tc (getTid rids sys)
                (getTaskChannelState sys (getTid rids sys) st)
                (applyAction sys (getTid rids sys) st)))"

(* -------- I n i t i a l   S t a t e   V C s --------------*)

text \<open>An initial state should satisfy all assertions tied to a ready IDs in the ready set\<close>

definition initStateVC :: "'value System \<Rightarrow> Model \<Rightarrow> 'value SystemSpec \<Rightarrow> bool"
  where "initStateVC sys m sysSpec \<equiv>
          ballAssert sysSpec (initSystemState sys) (ready (initSystemState sys))"

(* -------- S y s t e m     P r e   C o n d i t i o n      V C s --------------*)

text \<open>All pre assertions for a component transition should imply the pre-condition of the component\<close>

definition systemPreTaskVCHelper :: "'value System \<Rightarrow> 'value SystemSpec \<Rightarrow> 'value TaskContracts \<Rightarrow> 'value SystemState \<Rightarrow> Rids \<Rightarrow> bool"
  where "systemPreTaskVCHelper sys sysSpec con st rids \<equiv>
             \<comment> \<open>if a state satisfies all pre-assertions of a task transition\<close>  
             ballAssert sysSpec st rids 
             \<longrightarrow>
             \<comment> \<open>then the should state satisfy the precondition of the task transition\<close>
             ((taskPre con) $ getTid rids sys) 
                (fst (getTaskChannelState sys (getTid rids sys) st))
                (snd (getTaskChannelState sys (getTid rids sys) st))"

definition systemPreTaskVC :: "'value System \<Rightarrow> Model \<Rightarrow> 'value SystemSpec \<Rightarrow> 'value TaskContracts \<Rightarrow> Rids \<Rightarrow> bool"
  where "systemPreTaskVC sys m sysSpec con rids \<equiv>
          rids \<in> (dom (activationMap sys)) \<longrightarrow>
          (\<forall> (st :: 'value SystemState). systemPreTaskVCHelper sys sysSpec con st rids)"

(* -------- S y s t e m     P o s t   A s s e r t      V C s ------------------*)

definition systemNextAssertVCHelper_task :: "'value System \<Rightarrow> Model \<Rightarrow> 'value SystemSpec \<Rightarrow> 'value TaskContracts \<Rightarrow>
                                              'value WriteFrame \<Rightarrow> 'value SystemState \<Rightarrow> Rids 
                                              \<Rightarrow> Rid \<Rightarrow> bool"
  where "systemNextAssertVCHelper_task sys m sysSpec tc wrf st1 precedingPlaces followPlace \<equiv>
          \<forall>(st2 :: 'value SystemState). 
                       \<comment> \<open>if the pre assertions are true for st1\<close>
                       ballAssert sysSpec st1 precedingPlaces
                       \<comment> \<open>and the post condition holds for st1 and some st2\<close>
                       \<and> ((taskPost tc) $ (getTid precedingPlaces sys))
                            (fst (getTaskChannelState sys (getTid precedingPlaces sys) st1))
                            (snd (getTaskChannelState sys (getTid precedingPlaces sys) st1))
                            (systemTasks st2 $ (getTid precedingPlaces sys)) (systemChs st2)
                       \<comment> \<open>and st1 and st2 respects the local frame\<close>
                       \<and> (lFrame wrf $ (getTid precedingPlaces sys)) 
                            (getTaskChannelState sys (getTid precedingPlaces sys) st1)
                            ((systemTasks st2 $ (getTid precedingPlaces sys)), systemChs st2)
                       \<comment> \<open>and st1 and  st2 respects the global frame\<close>
                       \<and> (gFrame wrf $ (getTid precedingPlaces sys)) 
                            (systemTasks st1, systemChs st1)
                            (systemTasks st2, systemChs st2)
                       \<comment> \<open>then the post assertions should hold for st2\<close>
                       \<longrightarrow> ((sysPlaceAsserts sysSpec) $ followPlace) (systemTasks st2) (systemChs st2)"

definition systemNextAssertVCHelper_skip :: "'value System \<Rightarrow> 'value SystemSpec \<Rightarrow> 'value SystemState \<Rightarrow> Rids 
                                  \<Rightarrow> (Tid, 'value TaskState) map \<Rightarrow> 'value ChState \<Rightarrow> Rid \<Rightarrow> bool"
  where "systemNextAssertVCHelper_skip sys sysSpec st1 precedingPlaces tst' chst' followPlace \<equiv>
          \<comment> \<open>if the pre assertions are true for st1\<close>
          ballAssert sysSpec st1 precedingPlaces
          \<longrightarrow> 
          \<comment> \<open>then the post assertions st1\<close>
          ((sysPlaceAsserts sysSpec) $ followPlace) tst' chst'"

text \<open>Given a state that satisfies the pre-assertions of a transition:
        If the transition is a component transition then, the state resulting from applying the action should satisfy all post-assertions
        If the transition is a control point transition then, the original state should satisfy all post-assertions\<close>


definition systemNextAssertVC :: "'value System \<Rightarrow> Model \<Rightarrow> 'value SystemSpec \<Rightarrow> 'value TaskContracts \<Rightarrow> 
                                   'value WriteFrame \<Rightarrow> Rids \<Rightarrow> Rids \<Rightarrow> bool"
  where "systemNextAssertVC sys m sysSpec tc wrf precedingPlaces followPlaces \<equiv>
          \<forall> st. (\<forall>followPlace |\<in>| followPlaces. 
                  \<comment> \<open>if the transition is a task transition\<close>
                  (precedingPlaces \<in> (dom (activationMap sys)) \<longrightarrow>
                    systemNextAssertVCHelper_task sys m sysSpec tc wrf st precedingPlaces followPlace)
                  \<and>
                  \<comment> \<open>if the transition is a control point transition\<close>
                  (precedingPlaces \<notin> (dom (activationMap sys)) \<longrightarrow>
                    systemNextAssertVCHelper_skip sys sysSpec st precedingPlaces 
                      (systemTasks st)
                      (systemChs st)
                      followPlace))"

(* -------- P r e - P o s t   A s s e r t      V C s ------------------*)

text \<open>Because the cycle is cyclic the END Assertion needs to imply the START Assertion\<close>

definition postPreAssertVC :: "'value System \<Rightarrow> Model \<Rightarrow> 'value SystemSpec \<Rightarrow> bool"
  where "postPreAssertVC sys m sysSpec \<equiv> 
            \<forall>(st :: 'value SystemState). 
                  (((sysPlaceAsserts sysSpec) $ modelEndRid m) (systemTasks st) (systemChs st)
                  \<longrightarrow> 
                  ((sysPlaceAsserts sysSpec) $ modelStartRid m) (systemTasks st) (systemChs st))"


(* -------- C o m b i n e d      V C s --------------*)


definition ContractConformanceVCs :: "'value System \<Rightarrow> Model \<Rightarrow> 'value TaskContracts \<Rightarrow> 'value SystemSpec \<Rightarrow> MayHappenInParallelRel \<Rightarrow> 'value WriteFrame \<Rightarrow> bool"
  where "ContractConformanceVCs sys m cons sysSpec mhip wrf \<equiv>
          wf_MayHappenInParallelRel_dom sys mhip
          \<and> mayHappenInParallelInd mhip sys sysSpec
          \<and> wf_WriteFrame sys m wrf
          \<and> wf_TaskContracts sys m cons
          \<and> wf_SystemSpec sysSpec sys
          \<and> initStateVC sys m sysSpec
          \<and> postPreAssertVC sys m sysSpec
          \<and> (\<forall>ridsRel \<in> getAllTransition sys. systemPreTaskVC sys m sysSpec cons (getPrecedingPlaces ridsRel))
          \<and> (\<forall>ridsRel \<in> getAllTransition sys. systemNextAssertVC sys m sysSpec cons wrf (getPrecedingPlaces ridsRel) (getFollowingPlaces ridsRel))
          \<and> (\<forall>ridsRel \<in> getAllTransition sys. taskConVC sys m cons (getPrecedingPlaces ridsRel))"

(* -------- V C     S o u n d n e s s -------- *)

text \<open>Get all transitions parallel to rids transition\<close>
definition getInParallel :: "MayHappenInParallelRel \<Rightarrow> Rids \<Rightarrow> Rids set"
  where "getInParallel mhip rids = {r. (rids, r) \<in> mhip}"

text \<open>For the purposes of this tool soundness for VCs is defined as follows:
      . Given that the model and system are well formed and the transitions conform to the task
        and system requirements
      . If st1 satisfies all assertions tied to its schedule state then taking a single execution step
        produces a state, st2, that satisfies all assertions tied to its schedule state

      This is accomplished by creating the following case breakdown:
      . Task/Component Transition
        . Choice is {|END|}
        . Choice is not {|END|}
          . The set of in places for the transition
          . All other transitions that are fireable in ready st1
          . All other places not tied to a firedable transition in ready st1
      . Control Point/Skip Transition
        . Choice is {|END|}
          . Choice is not {|END|}
          . The set of in places for the transition
          . All other places not in the in places of the transition in ready st1 \<close>
lemma VCSoundness: 
  assumes wf_model: "wf_Model m"
      and wf_sys: "wf_System sys m"
      and nextAssms: "nextRel_Assumptions sys m"
      and wf_st1: "wf_SystemState m sys st1"
      and step: "systemStep sys m st1 st2"
      and conform: "ContractConformanceVCs sys m tc sysSpec mhip wrf"
      and mhipAssm: "MHIP_assumption mhip sys m"
      and bstrAssm: "BackStepReachability_Assumption sys m"
      and allPlaceAssert: "ballAssert sysSpec st1 (ready st1)"
    shows "ballAssert sysSpec st2 (ready st2)"
  using step
proof (cases)
  case (stepTask choice ready' tid tidAction tscs')
  assume a1: "choice \<in> {s. s |\<subseteq>| ready st1 \<and> (s \<in> dom (nextRel sys) \<or> s = {|modelEndRid m|})}"
  assume a2: "choice \<in> dom (activationMap sys)"
  assume a3: "ready' = scheduleNextTotal (nextRel sys) m (ready st1) choice"
  assume a4: "tid = the (activationMap sys choice)"
  assume a5: "tidAction = action (the (taskMap sys tid))"
  assume a6: "tscs' = do_action (the (systemTasks st1 tid), systemChs st1) tidAction"
  assume a7: "st2 = mkSystemState ((systemTasks st1)(tid \<mapsto> fst tscs')) (snd tscs') ready' (systemTasks st1) (systemChs st1)"

  \<comment> \<open>choice is either {|END|} or it is not\<close>
  have "choice = {|modelEndRid m|} \<or> choice \<noteq> {|modelEndRid m|}" by auto
  thus "ballAssert sysSpec st2 (ready st2)"
  proof
    assume "choice = {|modelEndRid m|}"

    \<comment> \<open>This holds trivially since {|END|} can never be a component transition\<close>
    from this a2 wf_sys show "ballAssert sysSpec st2 (ready st2)"
      apply (simp add: wf_System_def wf_System_ActivationMap_def wf_System_NextRel_def wf_System_NextRel_SourceAndSink_def)
      by (metis finsertCI)
  next
    assume notEnd: "choice \<noteq> {|modelEndRid m|}"

    \<comment> \<open>The out places of choice are in the schedule state of st2\<close>
    from a7 a3 notEnd have choiceCaries: "(nextRel sys) $ choice |\<subseteq>| (ready st2)"
      by (simp add: mkSystemState_def)
    \<comment> \<open>choice is a transition in NextRel\<close>
    from notEnd a1 have validChoice: "choice \<in> dom(nextRel sys)"
      by simp
    \<comment> \<open>All post assertions of choice are satisfied by st2\<close>
    have choiceHolds: "ballAssert sysSpec st2 ((nextRel sys) $ choice)"
    proof -
      \<comment> \<open>All pre-assertions of choice are true for st1\<close>
      from a1 allPlaceAssert have trueChoice: "ballAssert sysSpec st1 choice"
        by (smt (verit) ballAssert_def fin_mono mem_Collect_eq) 
      \<comment> \<open>choice -> nextRel sys $ choice is a transition in the petri net\<close>
      from validChoice have isTransisition: "(choice, nextRel sys $ choice) \<in> getAllTransition sys"
        using a1 getAllTransition_def by auto 
      \<comment> \<open>The systemPreTaskVC is true for the transition due to the contract conformance of the system\<close>
      from this conform have "systemPreTaskVC sys m sysSpec tc (getPrecedingPlaces (choice, the (nextRel sys choice)))"
        by (simp add: ContractConformanceVCs_def)
      \<comment> \<open>The precondition of the task tied to the transition is true for st1\<close>
      from a2 a4 this trueChoice conform have preTrue: "((taskPre tc) $ tid) 
                                                          (fst (getTaskChannelState sys tid st1)) 
                                                          (snd (getTaskChannelState sys tid st1))"
        by (auto simp add: systemPreTaskVC_def getPrecedingPlaces_def systemPreTaskVCHelper_def getTid_def)
      \<comment> \<open>The taskConVC is true for the transition due to the contract conformance of the system\<close>
      from this conform have "taskConVC sys m tc choice"
        using ContractConformanceVCs_def isTransisition getPrecedingPlaces_def by fastforce
      \<comment> \<open>The post-condition of the task tied to the transition is true for st1 and st2\<close>
      from this preTrue a2 a4 a5 a6 a7 conform have postTrue: "((taskPost tc) $ tid) 
                                              (fst (getTaskChannelState sys tid st1)) 
                                              (snd (getTaskChannelState sys tid st1))
                                              (fst (getTaskChannelState sys tid st2)) 
                                              (snd (getTaskChannelState sys tid st2))"
        by (auto simp add: taskConVC_def applyPrePost_def getTid_def getTaskChannelState_def 
                              mkSystemState_def applyAction_def getAction_def)
      \<comment> \<open>tid is in the domain of the local write frame\<close>
      from conform a2 a4 wf_sys have tidLFrame: "tid \<in> dom (lFrame wrf)"
        apply (simp add: ContractConformanceVCs_def wf_WriteFrame_def wf_WriteFrame_Dom_def
                              wf_System_def wf_System_ActivationMap_def wf_System_TaskMap_def)
        by (meson domIff in_mono option.exhaust_sel ranI)
      \<comment> \<open>the local write frame holds over the action tied to tid\<close>
      from this conform have "(lFrame wrf $ tid) (getTaskChannelState sys tid st1) (applyAction sys tid st1)"
        by (simp add: ContractConformanceVCs_def wf_WriteFrame_LocalExec_def wf_WriteFrame_def)
      \<comment> \<open>the local write frame holds for st1 and st2\<close>
      from this conform wf_sys a5 a6 a7 have LocF: "(lFrame wrf $ tid) 
                                          (getTaskChannelState sys tid st1) 
                                          (getTaskChannelState sys tid st2)"
        by (simp add: ContractConformanceVCs_def wf_WriteFrame_def wf_WriteFrame_LocalExec_def
                         mkSystemState_def getTaskChannelState_def applyAction_def getAction_def)
      \<comment> \<open>tid is in the domain of the global write frame\<close>
      from conform a2 a4 wf_sys have "tid \<in> dom (gFrame wrf)"
        using ContractConformanceVCs_def tidLFrame wf_WriteFrame_Dom_def wf_WriteFrame_def by blast 
      \<comment> \<open>the global write frame holds over the global action tied to tid\<close>
      from this conform have "(gFrame wrf $ tid) (systemTasks st1, systemChs st1) (applyActionGlobal sys tid st1)"
        by (simp add: ContractConformanceVCs_def wf_WriteFrame_GlobalExec_def wf_WriteFrame_def)
      \<comment> \<open>the global write frame holds for st1 and st2\<close>
      from this wf_sys a5 a6 a7 have GlobF: "(gFrame wrf $ tid) 
                                          (systemTasks st1, systemChs st1)
                                          (systemTasks st2, systemChs st2)"
        by (simp add: wf_WriteFrame_def wf_WriteFrame_GlobalExec_def
                      mkSystemState_def getTaskChannelState_def applyActionGlobal_def applyAction_def 
                      getAction_def)
      \<comment> \<open>the systemNextAssertVC is true for the transition due to contract conformance\<close>
      from conform have "systemNextAssertVC sys m sysSpec tc wrf choice ((nextRel sys) $ choice)"
        using ContractConformanceVCs_def getFollowingPlaces_def getPrecedingPlaces_def isTransisition by fastforce
      \<comment> \<open>Because systemNextAssertVC is true, the local and global frames hold, the post-condition for
        the task holds, and the pre-assertions hold, all post-assertions of choice are true for st2\<close>
      from this a2 a4 trueChoice postTrue LocF GlobF show ?thesis 
        by (auto simp add: systemNextAssertVC_def ballAssert_def getTaskChannelState_def
                         getTid_def systemNextAssertVCHelper_task_def trueChoice)
    qed
  
    \<comment> \<open>All pre-assertions for any alternate fireable transitions hold for st2\<close>
    have altChoiceHold: "\<forall>c \<in> {s. s |\<subseteq>| ready st1 - choice \<and> (s \<in> dom (nextRel sys) \<or> s = {|modelEndRid m|})}. ballAssert sysSpec st2 c"
    proof
      fix c
      assume cIsChoice: "c \<in> {s. s |\<subseteq>| ready st1 |-| choice \<and> (s \<in> dom (nextRel sys) \<or> s = {|modelEndRid m|})}"

      \<comment> \<open>the set of in places of choice is not empty\<close>
      from wf_sys a1 have choiceNotEmpty: "choice \<noteq> {||}" 
        by (auto simp add: wf_System_def wf_System_NextRel_def)
      \<comment> \<open>the alt choice c is not equal to choice\<close>
      from choiceNotEmpty cIsChoice have cChoiceNotEq: "c \<noteq> choice"
        by auto

      \<comment> \<open>c must a transition in NextRel\<close>
      have "c \<in> dom(nextRel sys)"
        apply (rule ccontr)
      proof -
        assume "c \<notin> dom (nextRel sys)"
        \<comment> \<open>c must be {|ENd|}\<close>
        from this cIsChoice have cIsEnd: "c = {|modelEndRid m|}"
          by simp
        \<comment> \<open>END must be a member of (ready st1)\<close>
        from this cIsChoice have "{|modelEndRid m|} |\<subseteq>| ready st1"
          by auto
        \<comment> \<open>By proper completion (ready st1) = {|END|}\<close>
        from this choiceCaries cChoiceNotEq nextAssms wf_st1 have "{|modelEndRid m|} = ready st1"
          by (auto simp add: wf_SystemState_def wf_SystemState_Reach_def nextRel_Assumptions_def 
                             wf_System_NextRel_ProperComplete_def)
        \<comment> \<open>Contradiction because choice is not {|END|} and choice is is (ready st1)\<close>
        from this a1 cIsChoice choiceNotEmpty cIsEnd show False
          by blast
      qed 

      \<comment> \<open>choice and c may happen in parallel\<close>
      from this validChoice cChoiceNotEq mhipAssm wf_st1 a1 cIsChoice have "(choice, c) \<in> mhip"
        by (auto simp add: MHIP_assumption_def wf_SystemState_def wf_SystemState_Reach_def)
      \<comment> \<open>therefore, choice and c are non blocking\<close>
      from this conform have nonB: "nonBlocking sys sysSpec choice c"
        by (auto simp add: ContractConformanceVCs_def mayHappenInParallelInd_def independent_def)

      \<comment> \<open>all pre-assertions of choice hold true for st1\<close>
      from a1 allPlaceAssert have trueChoice: "ballAssert sysSpec st1 choice"
        by (auto simp add: ballAssert_def)
      \<comment> \<open>all pre-assertions of c hold true for st1\<close>
      from a1 cIsChoice allPlaceAssert have trueC: "ballAssert sysSpec st1 c"
        by (auto simp add: ballAssert_def)

      \<comment> \<open>Because choice and c are non-blocking, all pre-assertions of c hold for the state that results
        from firing choice\<close>
      from trueChoice trueC nonB a2 have "ballAssertAlt sysSpec (applyActionGlobal sys (getTid choice sys) st1) c"
        by (simp add: nonBlocking_def)

      \<comment> \<open>all pre-assertions of c hold for st2 by construction from st1\<close>
      from this a4 a5 a6 a7 show "ballAssert sysSpec st2 c"
        by (simp add: ballAssert_def ballAssertAlt_def mkSystemState_def applyActionGlobal_def
                         applyAction_def getAction_def getTaskChannelState_def getTid_def)
    qed
  
    

    \<comment> \<open>there is a finite number of transitions\<close>
    from wf_sys have "finite (dom (nextRel sys))"
      by (auto simp add: wf_System_def wf_System_NextRel_def)
    \<comment> \<open>the set of fireable transition in st1 is finite\<close>
    from this wf_sys have "finite {s. s |\<subseteq>| ready st1 \<and> (s \<in> dom (nextRel sys) \<or> s = {|modelEndRid m|})}"
      by simp

    \<comment> \<open>For all places p in st1 that are not tied to a fireable transition, the assertion tied to p
      should hold for st2\<close>
    have ete: "\<forall>p \<in> fset (ready st1 - choice) - (\<Union> (fset`{s. s |\<subseteq>| ready st1 - choice \<and> (s \<in> dom (nextRel sys) \<or> s = {|modelEndRid m|})})).
          ((sysPlaceAsserts sysSpec) $ p) (systemTasks st2) (systemChs st2)"
    proof 
      fix p
      assume pLeft: "p \<in> fset (ready st1 |-| choice) - \<Union> (fset ` {s. s |\<subseteq>| ready st1 |-| choice \<and> (s \<in> dom (nextRel sys) \<or> s = {|modelEndRid m|})})"

      \<comment> \<open>p is in the schedule state of st1\<close>
      have pReady: "p |\<in>| (ready st1)" using pLeft by auto
      \<comment> \<open>p is a not an in place of choice\<close>
      have pNotChoice: "p |\<notin>| choice" using pLeft by auto
      \<comment> \<open>p is not in an in places of any fireable transition that is not choice\<close>
      have pNotC: "\<forall>c \<in> {s. s |\<subseteq>| ready st1 - choice \<and> (s \<in> dom (nextRel sys) \<or> s = {|modelEndRid m|})}. p |\<notin>| c" using pLeft by auto 

      \<comment> \<open>p does not equal END because there are other elements in the set. If it was END this would
        violate the Proper Completion WF condition\<close>
      have pNotEnd: "p \<noteq> modelEndRid m"
        apply (rule ccontr)
        using wf_sys wf_st1 nextAssms pLeft pReady pNotChoice 
        apply (simp add: nextRel_Assumptions_def wf_System_NextRel_ProperComplete_def wf_SystemState_def
                         wf_SystemState_Reach_def)
        using a1 fsubset_fsingletonD wf_System_NextRel_TransitionOnPath_def by fastforce

      \<comment> \<open>p is a Ready ID of the model\<close>
      from wf_st1 pReady have pIsRid: "p |\<in>| modelReadyIds m"
        by (auto simp add: wf_SystemState_def wf_SystemState_ReadySub_def)
      \<comment> \<open>p must in the union of the set of all in places since all model rids except END belong to this set\<close>
      from wf_sys pIsRid pNotEnd have "p \<in> \<Union> (fset ` dom (nextRel sys))"
        by (simp add: wf_System_def wf_System_NextRel_def wf_System_NextRel_DomUnion_def)
      \<comment> \<open>therefore there must exist a transition c (element of the domain) that has p as an in place\<close>
      from this have "\<exists>c \<in> dom(nextRel sys). p |\<in>| c"
        by simp

      then obtain c where obtainC: "c \<in> dom(nextRel sys) \<and> p |\<in>| c"
        by auto

      \<comment> \<open>c's in places cannot equal {|p|} otherwise it would be a fireable transition\<close>
      from this pReady pNotChoice pNotChoice pNotC have  "c \<noteq> {|p|}"
        by blast
      \<comment> \<open>therefore the cardinality of the set of in places of c is greater than one\<close>
      from this obtainC have sizeC: "fcard c > 1" 
        apply (auto simp add: fcard_def)
        by (meson card_le_Suc0_iff_eq finite_fset leI)
      \<comment> \<open>therefore, the transition must me a join transition (multiple inputs, one output)\<close>
      from this obtainC wf_sys have isJoin: "(fcard c > 1 \<and> fcard (nextRel sys $ c) = 1)"
        by (simp add: wf_System_def wf_System_NextRel_def wf_NextRel_AllPossibleTransitions_def 
                      wf_NextRel_Join_def)
      \<comment> \<open>therefore, there must exist a transition that is a sequent or join whose set of out places
        is {|p|} because p is an in place of a join transition\<close>
      from wf_sys isJoin obtainC have existC': "\<exists>c' \<in> dom (nextRel sys). 
                                  (nextRel sys $ c') = {|p|}
                                  \<and>
                                  (c' \<in> dom (activationMap sys) \<or> fcard c' > 1)"
        apply (simp add: wf_System_def wf_System_NextRel_def wf_NextRel_JoinPrev_def)
        by blast
  
      then obtain c' where origOfP: "c' \<in> dom (nextRel sys)
                                     \<and> (nextRel sys $ c') = {|p|}
                                     \<and> (c' \<in> dom (activationMap sys) \<or> fcard c' > 1)"
        by auto

      \<comment> \<open>the in places of choice does not equal the in places c by definition\<close>
      from obtainC pNotChoice have notEqC: "choice \<noteq> c"
        by auto    

      \<comment> \<open>The set out places for c' is {|p|}\<close>
      from origOfP have c'Res: "(nextRel sys $ c') = {|p|}" by auto
      \<comment> \<open>c' is a transition of nextRel\<close>
      from origOfP have c'Dom: "c' \<in> dom (nextRel sys)" by auto
      \<comment> \<open>the out places of c' are a subset of the schedule state of st1\<close>
      from pReady c'Res have subsetc': "the (nextRel sys c') |\<subseteq>| (ready st1)" by simp
      \<comment> \<open>the in places c' does not equal the in places of choice since a p is in the schedule state of st1\<close>
      from wf_st1 c'Dom c'Res pReady nextAssms a1 have notEqC': "c' \<noteq> choice"
        apply (simp add: nextRel_Assumptions_def wf_System_NoCycle_def wf_SystemState_def wf_SystemState_Reach_def)
        using subsetc' by blast

      \<comment> \<open>p is not an in place of c'\<close>
      from wf_sys c'Res have pNotEqC': "p |\<notin>| c'"
        apply (simp add: wf_System_def wf_System_NextRel_def wf_NextRel_NoReinsert_def)
        by (metis c'Dom finsert_absorb finsert_is_funion finsert_not_fempty finter_absorb1 funion_upper1)   

      \<comment> \<open>the in places of c and the in places of c' are not equal by definition\<close>
      have cNotEqC': "c \<noteq> c'"
        using obtainC pNotEqC' by auto

      \<comment> \<open>The in places of c' are not equal to the out places of c'\<close>
      from wf_sys have c'NotEqNext: "(nextRel sys $ c') \<noteq> c'"
        using c'Res pNotEqC' by auto

      \<comment> \<open>c must be a join transition by definition with the out places of c' being a subset of the 
       in places of c\<close>
      from cNotEqC' notEqC obtainC sizeC existC' origOfP 
      have cIsEndPath: "c \<in> dom (nextRel sys) \<and> fcard (c) > 1 
                        \<and> (nextRel sys $ c') |\<subseteq>| c 
                        \<and> c' \<noteq> c
                        \<and> choice \<noteq> c"
        by simp
        

      \<comment> \<open>therefore there exist a transition that satisfies the following constraints\<close>
      from this 
      have existEndPath: "\<exists>d \<in> dom (nextRel sys). fcard (d) > 1 \<and> (nextRel sys $ c') |\<subseteq>| d
                                                  \<and> c' \<noteq> d \<and> choice \<noteq> d"
        by auto  

      \<comment> \<open>the schedule state of st1 is reachable from {|START|} because it is well formed and 
        the in places of choice and the in places of c' are subset of the schedule state\<close>
      from c'Dom c'Res pReady a1 wf_st1
      have "scheduleReachBody (nextRel sys) {|modelStartRid m|} (ready st1) \<and> choice |\<subseteq>| (ready st1) \<and> the (nextRel sys c') |\<subseteq>| (ready st1)"
        by (auto simp add: wf_SystemState_def wf_SystemState_Reach_def)
      \<comment> \<open>therefore there exist a reachable schedule state that contains the in places of choice 
          and the in places of c' by the back step reachability assumption\<close>
      from this  notEqC' c'NotEqNext bstrAssm validChoice c'Dom  
      have choicec'Reach: "(\<exists>schst. scheduleReachBody (nextRel sys) {|modelStartRid m|} schst \<and> choice |\<subseteq>| schst \<and> c' |\<subseteq>| schst)"
        apply (simp add: BackStepReachability_Assumption_def)
        by (smt (verit, best) One_nat_def cIsEndPath subsetc')
      \<comment> \<open>therefore choice and c' mhip\<close>
      from this mhipAssm validChoice c'Dom notEqC' have cc'MHIP: "(choice, c') \<in> mhip"
        by (simp add: MHIP_assumption_def)
      \<comment> \<open>therefore choice and c' are independent\<close>     
      from conform cc'MHIP have cc'Ind: "independent sys sysSpec choice c'"
        by (auto simp add: ContractConformanceVCs_def mayHappenInParallelInd_def)

      \<comment> \<open>the assertion tied to place p is satisfied by st2\<close>
      then show "the (sysPlaceAsserts sysSpec p) (systemTasks st2) (systemChs st2)"
      proof-
        \<comment> \<open>Stating that a state satisfies all post assertions of c' is equivalent
          to stating that a state satisfies the assertion tied to p\<close>
        from origOfP have BpSysSpecEq: "\<forall>st. ballAssert sysSpec st (nextRel sys $ c') 
              = (sysPlaceAsserts sysSpec $ p) (systemTasks st) (systemChs st)"
          by (auto simp add: ballAssert_def)

        \<comment> \<open>Stating that a state satisfies all post assertions of c' is equivalent
          to stating that a state satisfies the assertion tied to p. 

          ballAssertAlt variation\<close>
        from origOfP have BpAltSysSpecEq: "\<forall>tscs. ballAssertAlt sysSpec tscs (nextRel sys $ c')
              = (sysPlaceAsserts sysSpec $ p) (fst tscs) (snd tscs)"
          by (auto simp add: ballAssertAlt_def)

        \<comment> \<open>st1 satisfies the post assertions of c' since p is a subset of (ready st1)\<close>
        from BpSysSpecEq pReady allPlaceAssert have baC: "ballAssert sysSpec st1 (nextRel sys $ c')"
          using ballAssert_def by blast
        \<comment> \<open>therefore st1 satisfies the assertion tied to p\<close>
        from this allPlaceAssert pReady have sysSpecC: "(sysPlaceAsserts sysSpec $ p) (systemTasks st1) (systemChs st1)"
          using ballAssert_def by blast

        \<comment> \<open>st1 satisfies the pre-assertions of choice since the in places of choice is a subset of (ready st1)\<close>
        from a1 allPlaceAssert have trueChoice: "ballAssert sysSpec st1 choice"
        by (smt (verit) ballAssert_def fin_mono mem_Collect_eq) 

        \<comment> \<open>Because st1 satisfies the post assertions of c' and the pre-assertions of choice and they
          are independent, firing the transition tied to choice should produce a state that satisfies
          the post assertions of c'\<close>
        from cc'Ind baC trueChoice a2 
        have "ballAssertAlt sysSpec (applyActionGlobal sys (getTid choice sys) st1) (nextRel sys $ c')"
          by (simp add: independent_def nonContradictPost_def)
        \<comment> \<open>therefore the resulting state should satisfy the assertion tied to p\<close>
        from this BpAltSysSpecEq have "(sysPlaceAsserts sysSpec $ p) 
                (fst (applyActionGlobal sys (getTid choice sys) st1)) 
                (snd (applyActionGlobal sys (getTid choice sys) st1))"
          by blast
        \<comment> \<open>therefore st2 satisfies the assertion tied to p by construction from st1\<close>
        from this BpSysSpecEq a1 a2 a3 a4 a5 a6 a7 show "the (sysPlaceAsserts sysSpec p) (systemTasks st2) (systemChs st2)"
          by (auto simp add: mkSystemState_def applyActionGlobal_def applyAction_def getAction_def
                                getTaskChannelState_def getTid_def)
      qed
    qed

    \<comment> \<open>schedule state of st2 is equal to the schedule state of st1 minus in places of choice and union
      of the out places of choice\<close>
    from a1 a2 a3 a7 validChoice have r2: "fset (ready st2) = fset (ready st1 - choice) \<union> fset ((nextRel sys) $ choice)"
      by (simp add: mkSystemState_def notEnd)

    \<comment> \<open>st2 satisfies the assertion of all places that are an in place for an alternate choice in the
      schedule state of st1\<close>
    from altChoiceHold have expandACH: "\<forall>p \<in> \<Union> (fset`{s. s |\<subseteq>| ready st1 - choice \<and> (s \<in> dom (nextRel sys) \<or> s = {|modelEndRid m|})}). 
                              ((sysPlaceAsserts sysSpec) $ p) (systemTasks st2) (systemChs st2)"
      by (auto simp add: ballAssert_def)

    \<comment> \<open>the schedule state of st1, minus the in places of choice, are the union of all in places of 
      alternate choices and all places not tied to a fireable transition in the schedule state of st1\<close>
    have "fset (ready st1 - choice) = 
             (\<Union> (fset`{s. s |\<subseteq>| ready st1 - choice \<and> (s \<in> dom (nextRel sys) \<or> s = {|modelEndRid m|})})) 
             \<union>
             (fset (ready st1 - choice) - (\<Union> (fset`{s. s |\<subseteq>| ready st1 - choice \<and> (s \<in> dom (nextRel sys) \<or> s = {|modelEndRid m|})})))"
      by blast
    \<comment> \<open>therefore, st2 satisfies all assertion tied to places in the schedule state of st1 that are not
      an in place of choice\<close>
    from ete altChoiceHold expandACH this have notChoiceHold: "\<forall>p \<in> fset (ready st1 - choice). ((sysPlaceAsserts sysSpec) $ p) (systemTasks st2) (systemChs st2)"
      by blast

    \<comment> \<open>st2 satisfies all post assertions of choice\<close>
    from choiceHolds have expandCH: "\<forall>p \<in> fset ((nextRel sys) $ choice). ((sysPlaceAsserts sysSpec) $ p) (systemTasks st2) (systemChs st2)"
      using ballAssert_def by blast

    \<comment> \<open>therefore, from expandCH notChoiceHold, st2 satisfies all assertions tied to its schedule state
      by construction of the schedule state\<close>
    from r2 notChoiceHold expandCH have "\<forall>p \<in> fset (ready st2). ((sysPlaceAsserts sysSpec) $ p) (systemTasks st2) (systemChs st2)"
      by auto
      
    thus ?thesis
      using ballAssert_def by fastforce
  qed
next
  case (stepSkip choice ready')
  assume a1: "choice \<in> {s. s |\<subseteq>| ready st1 \<and> (s \<in> dom (nextRel sys) \<or> s = {|modelEndRid m|})}"
  assume a2: "choice \<notin> dom (activationMap sys)"
  assume a3: "ready' = scheduleNextTotal (nextRel sys) m (ready st1) choice"
  assume a4: "st2 = mkSystemState (systemTasks st1) (systemChs st1) ready' (systemTasks st1) (systemChs st1)"

  \<comment> \<open>choice is {|END|} or it is not\<close>
  have "choice = {|modelEndRid m|} \<or> choice \<noteq> {|modelEndRid m|}" by simp
  
  thus "ballAssert sysSpec st2 (ready st2)"
  proof
    assume choiceIsEnd: "choice = {|modelEndRid m|}"

    \<comment> \<open>(ready st1 must equal {|END|} by proper completion)\<close>
    from this nextAssms a1 wf_st1 have st1Eq: "ready st1 = {|modelEndRid m|}"
      by (simp add: nextRel_Assumptions_def wf_System_NextRel_ProperComplete_def wf_SystemState_def
                    wf_SystemState_Reach_def)
    \<comment> \<open>therefore (ready st2) must be {|START|}\<close>
    from choiceIsEnd a4 a3 this have st2Eq: "ready st2 = {|modelStartRid m|}"
      by (simp add: mkSystemState_def)

    \<comment> \<open>st1 satisfies END Assert\<close>
    from st1Eq allPlaceAssert have "((sysPlaceAsserts sysSpec) $ modelEndRid m) (systemTasks st1) (systemChs st1)"    
      by (simp add: ballAssert_def)
    \<comment> \<open>therefore, st2 satisfies START Assert due to contract conformance\<close>
    from this a4 a3 conform have "((sysPlaceAsserts sysSpec) $ modelStartRid m) (systemTasks st2) (systemChs st2)" 
      by (simp add: ContractConformanceVCs_def postPreAssertVC_def mkSystemState_def)

    from this st2Eq show ?thesis 
      by (auto simp add: ballAssert_def)
  next
    assume notEnd: "choice \<noteq> {|modelEndRid m|}"

    \<comment> \<open>choice is a transition in nextRel\<close>
    from a1 notEnd have validChoice: "choice \<in> dom (nextRel sys)"
      by simp

    \<comment> \<open>The result of choice in the nextRel is in the schedule state of st2\<close>
    from a4 a3 notEnd have choiceCaries: "(nextRel sys) $ choice |\<subseteq>| (ready st2)"
      by (simp add: mkSystemState_def)
    \<comment> \<open>All assertions tied directly to stepping the schedule state are true for st2\<close>
    have choiceAssertHold: "ballAssert sysSpec st2 ((nextRel sys) $ choice)"
    proof -
      \<comment> \<open>All assertions tied to choice are true for st1\<close>
      from a1 allPlaceAssert have trueChoice: "ballAssert sysSpec st1 choice"
        by (smt (verit) ballAssert_def fin_mono mem_Collect_eq) 
      \<comment> \<open>choice -> nextRel sys $ choice is a transition in the petri net\<close>
      have isTransisition: "(choice, nextRel sys $ choice) \<in> getAllTransition sys"
        using a1 getAllTransition_def validChoice by auto 
      \<comment> \<open>the systemNextAssertVC is true for the transition due to contract conformance\<close>
      from conform have "systemNextAssertVC sys m sysSpec tc wrf choice ((nextRel sys) $ choice)"
        using ContractConformanceVCs_def getFollowingPlaces_def getPrecedingPlaces_def isTransisition by fastforce
      \<comment> \<open>Because systemNextAssertVC is true and the pre-assertions hold, all post-assertions that are 
          the direct result of the transition are true\<close>
      from this trueChoice a2 a3 a4 show ?thesis
        apply (simp add: systemNextAssertVC_def systemNextAssertVCHelper_skip_def mkSystemState_def ballAssert_def)
        by blast
    qed

    \<comment> \<open>all asserts tied to a place not in choice should hold for st2\<close>
    from a1 a2 a3 a4 have  assertFrame1: "\<forall>p |\<in>| ready st1. 
                                              p |\<notin>| choice 
                                              \<longrightarrow> 
                                              ((sysPlaceAsserts sysSpec) $ p) (systemTasks st2) (systemChs st2)"
      apply (simp add: mkSystemState_def)
      using allPlaceAssert ballAssert_def by blast
  
    \<comment> \<open>all asserts tied to a place not in choice should hold for st2\<close>
    from this have assertFrame2: "ballAssert sysSpec st2 (ready st1 |-| choice)"
      using ballAssert_def by force
  
    \<comment> \<open>ready st2 is the result of stepping the schedule and anything that is left behind from ready st1
        after stepping the schedule\<close>
    from a1 a2 a3 a4 validChoice notEnd have "ready st2 = ready st1 - choice |\<union>| (nextRel sys) $ choice"
      by (simp add: mkSystemState_def)
  
    \<comment> \<open>because ready st2 consists of all places remaining from st1 and the result of stepping the
        schedule and all assertions tied to both sets hold for st2, all ready assertions hold for st2\<close>
    from this a1 a2 a3 a4 choiceAssertHold assertFrame1 assertFrame2 ballAssertUnion show ?thesis
      using ballAssertUnion by metis 
  qed
qed


lemma multiStep_preserves_soundness: 
  "\<lbrakk>(systemStep sys m)\<^sup>*\<^sup>* st1 st2; 
    wf_Model m;
    wf_System sys m;
    nextRel_Assumptions sys m;
    ContractConformanceVCs sys m tc sysSpec mhip wrf;
    MHIP_assumption mhip sys m;
    BackStepReachability_Assumption sys m;
    wf_SystemState m sys st1;
    ballAssert sysSpec st1 (ready st1)\<rbrakk> \<Longrightarrow> ballAssert sysSpec st2 (ready st2)"
  apply (induction rule: rtranclp_induct)
  using VCSoundness multiStep_preserves_wellformedness apply (auto+)
  by blast

lemma systemReach_yields_soundness: 
  assumes model_wf: "wf_Model m"
     and sys_wf: "wf_System sys m"
     and reach: "systemReach sys m st"
     and nextAssms: "nextRel_Assumptions sys m"
     and conform: "ContractConformanceVCs sys m tc sysSpec mhip wrf"
     and mhipAssm: "MHIP_assumption mhip sys m"
     and bstrAssm: "BackStepReachability_Assumption sys m"
     and initState_wf: "wf_SystemState m sys (initSystemState sys)"
   shows "ballAssert sysSpec st (ready st)"
proof - 
  from reach have 
    multiStep: "((systemStep sys m)\<^sup>*\<^sup>* (initSystemState sys) st)" 
    by (simp add: systemReach_def)

  from conform have "ballAssert sysSpec (initSystemState sys) (ready (initSystemState sys)) "
    by (auto simp add: ContractConformanceVCs_def initStateVC_def)

  from this sys_wf initState_wf multiStep nextAssms bstrAssm conform mhipAssm show "ballAssert sysSpec st (ready st)"
    using multiStep_preserves_soundness model_wf
    by blast
qed
  

end