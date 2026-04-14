theory HAMRMicro04PythagoreanExample
  imports HAMRMicro04ExecutionSemantics HAMRMicro04Model HAMRMicro04Spec
begin

text \<open>The purpose of this example to is to provide a demonstration of the current VC framework for
      HAMRMicro04 along with show what needs to be added to provide a stronger proof system and
      things that need to be cleaned up with the current VC framework\<close>

text \<open>The example program simply takes in three arbitrary integers, squares them, and then checks
      if the three number are a pythagorean triple\<close>

section \<open>Channels\<close>

definition PythagCh :: "ChIds"
  where "PythagCh = {''x_in'',
                     ''y_in'',
                     ''z_in'',
                     ''x_sq'',
                     ''y_sq'',
                     ''z_sq'',
                     ''triple''}"

section \<open>Task Description\<close>

text \<open>Squaring Description\<close>

definition SquaringDescr :: "TaskDescr"
  where "SquaringDescr = \<lparr>
              inChIds = {''x_in'', ''y_in'', ''z_in''},
              outChIds = {''x_sq'', ''y_sq'', ''z_sq''},
              varIds = {} 
         \<rparr>"

text \<open>Triple Check Description\<close>

definition TripCheckDescr :: "TaskDescr"
  where "TripCheckDescr = \<lparr>
              inChIds = {''x_sq'', ''y_sq'', ''z_sq''},
              outChIds = {''triple''},
              varIds = {} 
         \<rparr>"

section \<open>Tasks\<close>

text \<open>Squaring\<close>

text \<open>Squaring takes in the integers and outputs the same integers squared\<close>

definition TID_Squaring :: "Tid" where "TID_Squaring = 1"

definition A_Squaring :: "int Action"
  where "A_Squaring TSCS = (fst TSCS, 
          (snd TSCS) ++ [''x_sq'' \<mapsto> (snd TSCS $ ''x_in'') * (snd TSCS $ ''x_in''),
                         ''y_sq'' \<mapsto> (snd TSCS $ ''y_in'') * (snd TSCS $ ''y_in''),
                         ''z_sq'' \<mapsto> (snd TSCS $ ''z_in'') * (snd TSCS $ ''z_in'')])"

definition Task_Squaring :: "int Task"
  where "Task_Squaring = mkTask TID_Squaring A_Squaring"

text \<open>Triple Check\<close>

text \<open>TripCheck takes in the squared numbers from Squaring and checks if x^2 + y^2 = z^2.
      TripCheck then return 1 if x^2 + y^2 = z^2 and 0 otherwise along the triple port\<close>

definition TID_TripCheck :: "Tid" where "TID_TripCheck = 2" 

definition A_TripCheck :: "int Action"
  where "A_TripCheck TSCS = (fst TSCS, 
          (snd TSCS) ++ [''triple'' \<mapsto> if ((snd TSCS $ ''x_sq'') + (snd TSCS $ ''y_sq'') = (snd TSCS $ ''z_sq''))
                                        then 1
                                        else 0])"

definition Task_TripCheck :: "int Task"
  where "Task_TripCheck = mkTask TID_TripCheck A_TripCheck"

text \<open>Task Map\<close>

definition PythagTaskMap :: "int TaskMap"
  where "PythagTaskMap = map_of [(TID_Squaring, Task_Squaring),
                                 (TID_TripCheck, Task_TripCheck)]"

section \<open>Model\<close>

definition PythagModel :: "Model"
  where "PythagModel = \<lparr> 
          modelTaskDescrs = map_of [(TID_Squaring, SquaringDescr),
                                    (TID_TripCheck, TripCheckDescr)],
          modelChIds = PythagCh
        \<rparr>"

section \<open>Schedule\<close>

definition PythagSchedule :: "Schedule"
  where "PythagSchedule = [TID_Squaring, TID_TripCheck]"

section \<open>Initial System State\<close>

text \<open>Squaring Initial Task State\<close>

definition initVarState_Squaring :: "int VarState"
  where "initVarState_Squaring = map_of []"

definition initTaskState_Squaring :: "int TaskState"
  where "initTaskState_Squaring = \<lparr>tvar = initVarState_Squaring\<rparr>"

text \<open>Triple Check Initial Task State\<close>

definition initVarState_TripCheck :: "int VarState"
  where "initVarState_TripCheck = map_of []"

definition initTaskState_TripCheck :: "int TaskState"
  where "initTaskState_TripCheck = \<lparr>tvar = initVarState_TripCheck\<rparr>"

text \<open>Initial Channel State\<close>

definition PythagInitChState :: "int ChState"
  where "PythagInitChState = map_of [(''x_in'', 0),
                                     (''y_in'', 0),
                                     (''z_in'', 0),
                                     (''x_sq'', 0),
                                     (''y_sq'', 0),
                                     (''z_sq'', 0),
                                     (''triple'', 1)]"

text \<open>Init System State\<close>

definition PythagInitSystemState :: "int SystemState" 
  where "PythagInitSystemState = \<lparr>
          systemTasks = map_of [(TID_Squaring, initTaskState_Squaring), (TID_TripCheck, initTaskState_TripCheck)],
          systemChs = PythagInitChState,
          scheduleState = initScheduleState PythagSchedule,
          previousSystemTasks = map_of [(TID_Squaring, initTaskState_Squaring), (TID_TripCheck, initTaskState_TripCheck)],
          previousSystemChs = PythagInitChState
        \<rparr>"

section \<open>System\<close>

definition PythagSystem :: "int System"
  where "PythagSystem = mkSystem PythagInitSystemState PythagTaskMap PythagSchedule"

section \<open>Well-Formedness\<close>

named_theorems Pythag_simps
lemmas [Pythag_simps] =
  PythagSystem_def
  PythagTaskMap_def
  PythagSchedule_def
  PythagModel_def
  PythagInitSystemState_def
  PythagInitChState_def
  initVarState_Squaring_def
  initTaskState_Squaring_def
  initVarState_TripCheck_def
  initTaskState_TripCheck_def
  TID_Squaring_def
  A_Squaring_def
  Task_Squaring_def
  TID_TripCheck_def
  A_TripCheck_def
  Task_TripCheck_def
  PythagCh_def
  SquaringDescr_def
  TripCheckDescr_def

lemma wf_PythagModel: "wf_Model PythagModel"
  by (auto simp add: Pythag_simps wf_Model_simps wf_TaskDescrs_simps initTid_def)

lemma wf_PythagSystem: "wf_System PythagSystem PythagModel"
  by (auto simp add: Pythag_simps wf_Model_simps wf_TaskDescrs_simps wf_System_simps initTid_def wf wf_ChState_def)

lemma wf_InitSystemState: "wf_SystemState PythagModel PythagSystem (initSystemState PythagSystem)"
  by (auto simp add: Pythag_simps wf_Model_simps wf_TaskDescrs_simps wf_System_simps wf_SystemState_simps wf_TaskState_def wf_ChState_def wf_VarState_dom_def wf_ScheduleState_simps)

section \<open>Specification\<close>

subsection \<open>Schedule Contract\<close>

text \<open>First, we establish the set of task IDs that the scheduling step
could possibly return. (Note: it turns out that we don't use this property
directly, but instead rely on a similar property for actions.  So we might
consider if this property should be dropped.)\<close>

lemma PythagSystem_scheduleNext_cases: 
  assumes wf_ScheduleState: "wf_ScheduleState PythagSystem schst" 
     and scheduleNext: "scheduleNext (schedule PythagSystem) schst = schst'"
   shows "currTid schst' = TID_Squaring \<or> currTid schst' = TID_TripCheck"
proof - 
  from  wf_PythagSystem wf_ScheduleState scheduleNext 
  have tids_in_system: "currTid schst' \<in> systemTids PythagSystem" 
    using scheduleNext_preserves_wf wf_ScheduleState_currTid_inSys_def  wf_PythagModel by blast    
  from tids_in_system show ?thesis by (auto simp add: Pythag_simps)
qed

text \<open>Next, we establish the set of actions that the system
could execute in a single step.\<close>

lemma PythagSystem_systemStep_cases: 
  assumes wf_SystemState: "wf_SystemState PythagModel PythagSystem st1"
      and step: "systemStep PythagSystem st1 st2"
  shows "(((systemTasks st2) $ (currTidSystemState st2), systemChs st2) = (do_action ((systemTasks st1) $ (nextTidSystemState PythagSystem st1), systemChs st1) A_Squaring)
     \<or>   ((systemTasks st2) $ (currTidSystemState st2), systemChs st2) = (do_action ((systemTasks st1) $ (nextTidSystemState PythagSystem st1), systemChs st1) A_TripCheck)
      )"
proof -
 \<comment> \<open>Name the intermediate elements of a system step\<close>
  obtain systemTasks1 systemChs1 taskState' tid tidAction tscs scheduleState2 systemTasks2 systemChs2 where
    p0: "systemTasks1 = systemTasks st1" and
    p1: "systemChs1 = systemChs st1" and
    p2: "scheduleState2 = scheduleNext (schedule PythagSystem) (scheduleState st1)" and
    p2a: "tid = (currTid scheduleState2)" and
    p3: "tidAction = action ((taskMap PythagSystem) $ tid)" and
    p4: "taskState' = systemTasks1 $ tid" and
    p5: "tscs = do_action (taskState', systemChs1) tidAction" and
    p5a: "systemTasks2 = systemTasks1 (tid \<mapsto> fst tscs)" and
    p5b: "systemChs2 = snd tscs" and
    p6: "st2 = mkSystemState systemTasks2 systemChs2 scheduleState2 systemTasks1 systemChs1"
    using step
    by (metis systemStep.simps)
  from  wf_PythagSystem wf_PythagModel wf_SystemState p2 p2a
  have currTid2_in_Ex1: "tid \<in> systemTids PythagSystem" 
    using wf_SystemState_def 
          scheduleNext_preserves_wf 
          wf_ScheduleState_currTid_inSys_def
    by blast
  \<comment> \<open>Therefore, looking up the tid in the task action structure will yield
  an action that is part of the system.\<close>
  from currTid2_in_Ex1 p3 
  have action_cases: "tidAction = A_Squaring \<or> tidAction = A_TripCheck" 
    by (auto simp add: Pythag_simps)
  from action_cases p5 p6 show ?thesis
    by (metis SystemState.select_convs(1,2,3) currTidSystemState.simps fun_upd_def mkSystemState_def nextTidSystemState.simps option.sel p0 p1 p2 p2a p4 p5a p5b prod.collapse) 
qed

subsection \<open>Pythagorean Triple Properties\<close>

text \<open>Define a scheduling contract.\<close>

definition PythagMayFollow :: "ScheduleMayFollow" where
"PythagMayFollow \<equiv> 
  mkCRel{(initTid, TID_Squaring), (TID_Squaring, TID_TripCheck), (TID_TripCheck, TID_Squaring)}"

definition PythagScheduleContract :: "ScheduleContracts" where
  "PythagScheduleContract \<equiv> mkScheduleContracts PythagMayFollow"

named_theorems Pythag_ScheduleContract_simps
lemmas [Pythag_ScheduleContract_simps] =
  PythagMayFollow_def
  PythagScheduleContract_def

lemma PythagScheduleContracts_wf: "wf_ScheduleContracts PythagSystem PythagScheduleContract"
  by (auto simp add: wf_ScheduleContracts_def Pythag_simps Pythag_ScheduleContract_simps)

text \<open>Show that the scheduling contract above satisfies framework verification
conditions, i.e., show that the task order indicated by the scheduling contract
is a sound abstraction of the actual task scheduling.\<close>

lemma Pythag_ScheduleContractsVC:
  "ScheduleContractsVC PythagSystem PythagModel PythagScheduleContract"
  unfolding ScheduleContractsVC_def
  apply clarify
proof -
  fix schst
  assume wf_sys: "wf_System PythagSystem PythagModel"
  assume wf_schons: "wf_ScheduleContracts PythagSystem PythagScheduleContract"
  assume wf_schst: "wf_ScheduleState PythagSystem schst"
  from wf_schst have slotNumRange: "0 \<le> (nextSlotNum schst) \<and> (nextSlotNum schst) < (length (schedule PythagSystem))"
    unfolding wf_ScheduleState_def wf_ScheduleState_nextSlotNum_def by blast
  from slotNumRange have slotNumValues: "nextSlotNum schst \<in> {0,1}"
    by (auto simp add: Pythag_simps)
  show "mayFollow PythagScheduleContract (currTid schst) (currTid (scheduleNext (schedule PythagSystem) schst))"
    using slotNumValues
    using wf_schst apply (auto simp add: wf_ScheduleState_simps Pythag_ScheduleContract_simps Pythag_simps)
    done
qed

subsection TaskContracts

text \<open>Note: TaskContracts have not been fully implemented in the framework for Post and InitPost 
            so they are set to True\<close>

text \<open>initPost\<close>

definition PythagInitPost :: "int TaskState \<Rightarrow> int ChState \<Rightarrow> bool"
  where "PythagInitPost ts cs \<equiv> True"

text \<open>Task Squaring\<close>

text \<open>All inputs to Squaring must be positive\<close>

definition PythagSquaringPre :: "int TaskState \<Rightarrow> int ChState \<Rightarrow> bool"
  where "PythagSquaringPre ts cs \<equiv> (cs $ ''x_in'') \<ge> 0 \<and> (cs $ ''y_in'') \<ge> 0 \<and> (cs $ ''z_in'') \<ge> 0"

definition PythagSquaringPost :: "int TaskState \<Rightarrow> int ChState \<Rightarrow> int TaskState \<Rightarrow> int ChState \<Rightarrow> bool"
  where "PythagSquaringPost tsPre csPre tsPost csPost \<equiv> True"

text \<open>Task Triple Check\<close>

text \<open>All inputs to TripCheck must be positive\<close>

definition PythagTripCheckPre :: "int TaskState \<Rightarrow> int ChState \<Rightarrow> bool"
  where "PythagTripCheckPre ts cs \<equiv> (cs $ ''x_sq'') \<ge> 0 \<and> (cs $ ''y_sq'') \<ge> 0 \<and> (cs $ ''z_sq'') \<ge> 0"

definition PythagTripCheckPost :: "int TaskState \<Rightarrow> int ChState \<Rightarrow> int TaskState \<Rightarrow> int ChState \<Rightarrow> bool"
  where "PythagTripCheckPost tsPre csPre tsPost csPost \<equiv> True"

text \<open>Aggregate Contract\<close>

definition PythagTaskPreMap :: "(Tid, int TaskPre) map"
  where "PythagTaskPreMap \<equiv>
    map_of [(TID_Squaring, PythagSquaringPre),
            (TID_TripCheck, PythagTripCheckPre)]"

definition PythagTaskPostMap :: "(Tid, int TaskPost) map"
  where "PythagTaskPostMap \<equiv>
    map_of [(TID_Squaring, PythagSquaringPost),
            (TID_TripCheck, PythagTripCheckPost)]"

definition PythagTaskContracts :: "int TaskContracts"
  where "PythagTaskContracts \<equiv> (mkTaskContracts PythagInitPost PythagTaskPreMap PythagTaskPostMap)"

named_theorems PythagTaskContracts_simps
lemmas [PythagTaskContracts_simps] = 
  PythagInitPost_def
  PythagSquaringPre_def
  PythagSquaringPost_def
  PythagTripCheckPre_def
  PythagTripCheckPost_def
  PythagTaskPreMap_def
  PythagTaskPostMap_def
  PythagTaskContracts_def

text \<open>Task Contracts Well-Formedness\<close>

lemma PythagTaskContracts_wf: "wf_TaskContracts PythagSystem PythagTaskContracts"
  by (simp add: wf_TaskContracts_def Pythag_simps PythagTaskContracts_simps)

subsection \<open>Component Specification\<close>

(* 
The general intuition for the current VC framework is that you take a slice of the schedule ordering 
(a task ordering) established in the schedule contract (preferably over a subsystem). The system
requires that you provide:
  . a precondition for the subsystem
  . a precondition and post-condition for an abstract function for a specific out-port of the subsystem
  . pre and post conditions for each task
  . post assertions for each task

The VCs are then generated following the hoare logic for concurrent systems established by 
Owiki and Gries where tasks that have no specific partial ordering relative to each other 
are treated as though they are run in parallel thus following the cobegin rule.
*)


text \<open>Task Ordering\<close>

text \<open>For this example we wi\<close>

text \<open>Component Contract over TID_Squaring to TID_TripCheck\<close>

definition PythagSystemTaskOrdering :: "TaskOrdering" where
  "PythagSystemTaskOrdering \<equiv> mkCRel {(TID_Squaring, TID_TripCheck)}"

text \<open>Component precondtion\<close>

text \<open>All inputs to the system must be positive\<close>

definition PythagSystemPre :: "int SystemState \<Rightarrow> bool"
  where "PythagSystemPre st \<equiv> (systemChs st) $ ''x_in'' \<ge> 0 \<and> (systemChs st) $ ''y_in'' \<ge> 0 \<and> (systemChs st) $ ''z_in'' \<ge> 0"

text \<open>Triple Pre Condition\<close>

text \<open>All inputs to the system must be positive\<close>

definition Triple_Pythag_Pre :: "int SystemState \<Rightarrow> bool"
  where "Triple_Pythag_Pre st \<equiv> (systemChs st) $ ''x_in'' \<ge> 0 \<and> (systemChs st) $ ''y_in'' \<ge> 0 \<and> (systemChs st) $ ''z_in'' \<ge> 0"

text \<open>Squaring Post Assert\<close>

text \<open>Following the execution of Squaring the _sq ports show be equal to _in ^ 2 for the respective port\<close>

definition Squaring_Pythag_End :: "int SystemState \<Rightarrow> bool"
  where "Squaring_Pythag_End st \<equiv> ((systemChs st) $ ''x_sq'') = ((systemChs st) $ ''x_in'') * ((systemChs st) $ ''x_in'') 
                                  \<and> ((systemChs st) $ ''y_sq'') = ((systemChs st) $ ''y_in'') * ((systemChs st) $ ''y_in'')
                                  \<and> ((systemChs st) $ ''z_sq'') = ((systemChs st) $ ''z_in'') * ((systemChs st) $ ''z_in'')"

text \<open>TripCheck Post Assert\<close>

text \<open>If x^2 + y^2 = z^2 then 1 should be on the triple port and 0 otherwise\<close>

definition TripCheck_Pythag_End :: "int SystemState \<Rightarrow> bool"
  where "TripCheck_Pythag_End st \<equiv> ((((systemChs st) $ ''x_sq'') + ((systemChs st) $ ''y_sq'') = ((systemChs st) $ ''z_sq'')) \<longrightarrow> (((systemChs st) $ ''triple'') = 1))
                                   \<and> ((((systemChs st) $ ''x_sq'') + ((systemChs st) $ ''y_sq'') \<noteq> ((systemChs st) $ ''z_sq'')) \<longrightarrow> (((systemChs st) $ ''triple'') = 0))"

text \<open>Combined Post Assert\<close>

definition Pythag_End :: "(Tid, int SystemAssert) map"
  where "Pythag_End \<equiv> map_of [(TID_Squaring, Squaring_Pythag_End), (TID_TripCheck, TripCheck_Pythag_End)]"

text \<open>Triple Post Condition\<close>

text \<open>If x^2 + y^2 = z^2 then 1 should be on the triple port and 0 otherwise\<close>

definition Triple_Pythag_Post :: "int SystemState \<Rightarrow> bool"
  where "Triple_Pythag_Post st \<equiv> ((((systemChs st) $ ''x_sq'') + ((systemChs st) $ ''y_sq'') = ((systemChs st) $ ''z_sq'')) \<longrightarrow> (((systemChs st) $ ''triple'') = 1))
                                 \<and> ((((systemChs st) $ ''x_sq'') + ((systemChs st) $ ''y_sq'') \<noteq> ((systemChs st) $ ''z_sq'')) \<longrightarrow> (((systemChs st) $ ''triple'') = 0))"

text \<open>Pythagorean Triple Subsystem Specification\<close>

definition PythagSysSpec :: "int SystemSpec"
  where "PythagSysSpec \<equiv> mkSysSpec PythagSystemTaskOrdering PythagSystemPre Triple_Pythag_Pre Pythag_End Triple_Pythag_Post"

named_theorems PythagCompSpec_simps
lemmas [PythagCompSpec_simps] =
  PythagSystemTaskOrdering_def
  PythagSystemPre_def
  Triple_Pythag_Pre_def
  Squaring_Pythag_End_def
  Pythag_End_def
  TripCheck_Pythag_End_def
  Triple_Pythag_Post_def
  PythagSysSpec_def

text \<open>Subsystem Specification Well-Formedness\<close>

lemma PythagSubSysSpec_wf: "wf_SystemSpec PythagSysSpec PythagSystem PythagScheduleContract"
  by (auto simp add: PythagCompSpec_simps Pythag_simps wf_SystemSpec_simps 
                     TaskOrdering_simps Pythag_ScheduleContract_simps mkSysSpec_def)

text \<open>Component VCs\<close>

(* ---------------- PreVC ---------------- *)

text \<open>Outputs:
        funPreVC: Pythag System Precondition --> Triple Function Precondition\<close>

lemma TriplePreVC: "funPreVC PythagSystem PythagSysSpec st"                                        
  by (auto simp add: funPreVC_def mkSysSpec_def PythagCompSpec_simps) 

text \<open>Outputs:
        startPreVC: Triple Function Precondition --> Squaring Precondition\<close>

lemma SquaringPre_sat: "startPreVC PythagSystem PythagSysSpec PythagTaskContracts st TID_Squaring"
  by (auto simp add: startPreVC_def mkSysSpec_def PythagCompSpec_simps PythagTaskContracts_simps )

text \<open>Outputs:
        taskPreVC: Squaring Post-Assertion --> Triple Check Precondition\<close>

lemma TripCheckPre_sat: "taskPreSysVC PythagSystem PythagSysSpec PythagTaskContracts st TID_TripCheck"
  unfolding taskPreSysVC_def
proof (auto simp add: PythagTaskContracts_def TID_TripCheck_def PythagTaskPreMap_def TID_Squaring_def)
  assume a1: "foldPostAssert PythagSysSpec st 2"
    
  from a1 have conjPost: "Squaring_Pythag_End st" 
    by (simp add: Pythag_simps PythagCompSpec_simps foldPostAssert_def mkSysSpec_def)

  from conjPost show "PythagTripCheckPre (the (systemTasks st 2)) (systemChs st)"
    by (simp add: PythagCompSpec_simps PythagTripCheckPre_def)
qed

text \<open>Outputs:
  funPreVC: Pythag System Precondition --> Triple Function Precondition
  startPreVC: Triple Function Precondition --> Squaring Preconditionn
  taskPreVC: Squaring Post-Assertion --> Triple Check Precondition\<close>

lemma preVC:
  assumes tidInSys: "tid \<in> set (schedule PythagSystem)"
  shows "taskPreVC PythagSystem PythagModel PythagScheduleContract PythagTaskContracts PythagSysSpec tid"
  unfolding taskPreVC_def
  apply clarify
proof
  fix st
  show "wf_SystemState PythagModel PythagSystem st \<Longrightarrow>
          mayFollow PythagScheduleContract (currTidSystemState st) tid \<Longrightarrow>
          tid \<in> getAllPoints (taskOrder PythagSysSpec) \<Longrightarrow> 
          tid \<in> getStartPoints (taskOrder PythagSysSpec) \<longrightarrow> startPreVC PythagSystem PythagSysSpec PythagTaskContracts st tid \<and> funPreVC PythagSystem PythagSysSpec st"
  proof
    assume wf_st: "wf_SystemState PythagModel PythagSystem st"
    assume mf: "mayFollow PythagScheduleContract (currTidSystemState st) tid"
    assume startPoint: "tid \<in> getStartPoints (taskOrder PythagSysSpec)"
    from startPoint have tidPossible: "tid \<in> {TID_Squaring}"
      by (auto simp add: getStartPoints_def PythagCompSpec_simps mkSysSpec_def)
    from tidPossible show "startPreVC PythagSystem PythagSysSpec PythagTaskContracts st tid \<and> funPreVC PythagSystem PythagSysSpec st"
      using TriplePreVC SquaringPre_sat by auto
  qed
next
  fix st
  show "wf_SystemState PythagModel PythagSystem st \<Longrightarrow>
          mayFollow PythagScheduleContract (currTidSystemState st) tid \<Longrightarrow> 
          tid \<in> getAllPoints (taskOrder PythagSysSpec) \<Longrightarrow> 
          tid \<notin> getStartPoints (taskOrder PythagSysSpec) \<longrightarrow> taskPreSysVC PythagSystem PythagSysSpec PythagTaskContracts st tid"
  proof
    assume wf_st: "wf_SystemState PythagModel PythagSystem st"
    assume mf: "mayFollow PythagScheduleContract (currTidSystemState st) tid"
    assume tid1: "tid \<in> getAllPoints (taskOrder PythagSysSpec)"
    assume tid2: "tid \<notin> getStartPoints (taskOrder PythagSysSpec)"
    from tid1 tid2 have tidPossible: "tid \<in> {TID_TripCheck}"
      by (auto simp add: getStartPoints_def getAllPoints_def PythagCompSpec_simps mkSysSpec_def)
    from tidPossible show "taskPreSysVC PythagSystem PythagSysSpec PythagTaskContracts st tid"
      apply auto
    proof -
      assume "tid = TID_TripCheck"
      from TripCheckPre_sat show "taskPreSysVC PythagSystem PythagSysSpec PythagTaskContracts st TID_TripCheck" by auto
    qed
  qed
qed

(* ---------------- Post ---------------- *)

(* Harder to argue across an action since system assertions can only look at the current state and
   cannot properly reason against a previous state. This can also be fixed by adding a log which
   is the next thing planned. For now, I am just relying on a sudo-frame condition*)

text \<open>Output:
        startPostAssertVC: Triple Function Precondition --> Squaring Post-Assertion\<close>

lemma SquaringPost_sat: "\<lbrakk>Triple_Pythag_Pre st1; do_action ((systemTasks st1) $ TID_Squaring, systemChs st1) A_Squaring = ((systemTasks st2) $ TID_Squaring, systemChs st2)\<rbrakk> \<Longrightarrow> Squaring_Pythag_End st2"
  apply (auto simp add: A_Squaring_def Squaring_Pythag_End_def PythagSysSpec_def mkSysSpec_def Triple_Pythag_Pre_def)
    apply (smt (z3) char.inject fun_upd_other fun_upd_same list.inject option.sel)
  apply (smt (z3) char.inject fun_upd_other fun_upd_same list.inject option.sel)
  by (smt (z3) char.inject fun_upd_other fun_upd_same list.inject option.sel)

lemma PythagSquaringPost_satisfied_step:
  assumes wf_st: "wf_SystemState PythagModel PythagSystem st1"
      and step: "systemStep PythagSystem st1 st2"
      and currTidTID1: "currTid (scheduleState st2) = TID_Squaring"
    shows "startPostAssertVC PythagSystem PythagSysSpec PythagTaskContracts TID_Squaring st1 st2"
  unfolding startPostAssertVC_def
proof (simp add: PythagSysSpec_def mkSysSpec_def Pythag_End_def)
  obtain systemTasks1 systemChs1 taskState' tid tidAction tscs scheduleState2 systemTasks2 systemChs2 where
    p0: "systemTasks1 = systemTasks st1" and
    p1: "systemChs1 = systemChs st1" and
    p2: "scheduleState2 = scheduleNext (schedule PythagSystem) (scheduleState st1)" and
    p2a: "tid = (currTid scheduleState2)" and
    p3: "tidAction = action ((taskMap PythagSystem) $ tid)" and
    p4: "taskState' = systemTasks1 $ tid" and
    p5: "tscs = do_action (taskState', systemChs1) tidAction" and
    p5a: "systemTasks2 = systemTasks1 (tid \<mapsto> fst tscs)" and
    p5b: "systemChs2 = snd tscs" and
    p6: "st2 = mkSystemState systemTasks2 systemChs2 scheduleState2 systemTasks1 systemChs1"
    using step
    by (metis systemStep.simps)
  from currTidTID1 p2 p2a p6 have tidisTIDSquaring: "tid = TID_Squaring"
    by (simp add: mkSystemState_def)
  from tidisTIDSquaring p3 have tidActionisASquaring: "tidAction = A_Squaring" by (simp add: Pythag_simps)
  from p0 p1 p4 p5 p5a p5b p6 tidisTIDSquaring tidActionisASquaring have ASquaringExec: "do_action ((systemTasks st1) $ TID_Squaring, systemChs st1) A_Squaring = ((systemTasks st2) $ TID_Squaring, systemChs st2)"
    by (simp add: mkSystemState_def)
  show "Triple_Pythag_Pre st1 \<longrightarrow> Squaring_Pythag_End st2"
  proof
    assume precond: "Triple_Pythag_Pre st1"
    from precond ASquaringExec show "Squaring_Pythag_End st2"
      using SquaringPost_sat by auto 
  qed
qed


text \<open>Output:
        taskPostAssertVC: Squaring Post-Assertion --> Triple Check Post-Assertion\<close>

lemma TripCheckPost_sat: "\<lbrakk>foldPostAssert PythagSysSpec st1 TID_TripCheck; 
                           do_action ((systemTasks st1) $ TID_TripCheck, systemChs st1) A_TripCheck = ((systemTasks st2) $ TID_TripCheck, systemChs st2) \<rbrakk> 
                           \<Longrightarrow> TripCheck_Pythag_End st2"
  unfolding TripCheck_Pythag_End_def
proof -
  assume foldedPost: "foldPostAssert PythagSysSpec st1 TID_TripCheck"
  assume act: "do_action (the (systemTasks st1 TID_TripCheck), systemChs st1) A_TripCheck = (the (systemTasks st2 TID_TripCheck), systemChs st2)"

  from foldedPost have conjPost: "Squaring_Pythag_End st1"  
    by (simp add: Pythag_simps PythagCompSpec_simps foldPostAssert_def mkSysSpec_def)

  from act conjPost show "(the (systemChs st2 ''x_sq'') + the (systemChs st2 ''y_sq'') = the (systemChs st2 ''z_sq'') \<longrightarrow> the (systemChs st2 ''triple'') = 1) \<and>
                          (the (systemChs st2 ''x_sq'') + the (systemChs st2 ''y_sq'') \<noteq> the (systemChs st2 ''z_sq'') \<longrightarrow> the (systemChs st2 ''triple'') = 0)"
    apply (auto simp add: A_TripCheck_def Squaring_Pythag_End_def PythagSysSpec_def mkSysSpec_def Triple_Pythag_Pre_def)
     apply (smt (z3) char.inject fun_upd_other fun_upd_same list.inject option.sel)
    by (smt (z3) char.inject fun_upd_other fun_upd_same list.inject option.sel)
qed

lemma PythagTripCheckPost_satisfied_step:
  assumes wf_st: "wf_SystemState PythagModel PythagSystem st1"
      and step: "systemStep PythagSystem st1 st2"
      and currTidTID1: "currTid (scheduleState st2) = TID_TripCheck"
    shows "taskPostAssertVC PythagSystem PythagSysSpec PythagTaskContracts TID_TripCheck st1 st2"
  unfolding taskPostAssertVC_def
proof -
  obtain systemTasks1 systemChs1 taskState' tid tidAction tscs scheduleState2 systemTasks2 systemChs2 where
    p0: "systemTasks1 = systemTasks st1" and
    p1: "systemChs1 = systemChs st1" and
    p2: "scheduleState2 = scheduleNext (schedule PythagSystem) (scheduleState st1)" and
    p2a: "tid = (currTid scheduleState2)" and
    p3: "tidAction = action ((taskMap PythagSystem) $ tid)" and
    p4: "taskState' = systemTasks1 $ tid" and
    p5: "tscs = do_action (taskState', systemChs1) tidAction" and
    p5a: "systemTasks2 = systemTasks1 (tid \<mapsto> fst tscs)" and
    p5b: "systemChs2 = snd tscs" and
    p6: "st2 = mkSystemState systemTasks2 systemChs2 scheduleState2 systemTasks1 systemChs1"
    using step
    by (metis systemStep.simps)
  from currTidTID1 p2 p2a p6 have tidisTIDTripCheck: "tid = TID_TripCheck"
    by (simp add: mkSystemState_def)
  from tidisTIDTripCheck p3 have tidActionisATripCheck: "tidAction = A_TripCheck" by (simp add: Pythag_simps)
  from p0 p1 p4 p5 p5a p5b p6 tidisTIDTripCheck tidActionisATripCheck have ATripCheckExec: "do_action ((systemTasks st1) $ TID_TripCheck, systemChs st1) A_TripCheck = ((systemTasks st2) $ TID_TripCheck, systemChs st2)"
    by (simp add: mkSystemState_def)
  show "foldPostAssert PythagSysSpec st1 TID_TripCheck \<longrightarrow> the (sysTasksAsserts PythagSysSpec TID_TripCheck) st2"
  proof clarify
    assume precond: "foldPostAssert PythagSysSpec st1 TID_TripCheck"

    from precond ATripCheckExec have "TripCheck_Pythag_End st2"
      using TripCheckPost_sat by auto 

    thus "the (sysTasksAsserts PythagSysSpec TID_TripCheck) st2" by (auto simp add: Pythag_simps PythagCompSpec_simps mkSysSpec_def)
  qed
qed

(* NEED TO SOMEWAY TO PROVE THIS IN A CONSISTENT MANNER *)

text \<open>Output:
        startPostAssertVC: Triple Function Precondition --> Squaring Post-Assertion
        taskPostAssertVC: Squaring Post-Assertion --> Triple Check Post-Assertion\<close>

lemma postVC: 
  assumes tidInSys: "tid \<in> systemTids PythagSystem"
  shows "taskPostVC PythagSystem PythagModel PythagTaskContracts PythagSysSpec tid"
  unfolding taskPostVC_def
  apply clarify
proof
  fix st1 st2
  assume wf_st: "wf_SystemState PythagModel PythagSystem st1"
  assume step: "systemStep PythagSystem st1 st2"
  assume inFlow: "currTidSystemState st2 \<in> getAllPoints (taskOrder PythagSysSpec)"
  assume currTid: "tid = currTidSystemState st2"
  from tidInSys have tidset: "tid \<in> {TID_Squaring, TID_TripCheck}"
    by (simp add: Pythag_simps)

  show "currTidSystemState st2 \<in> getStartPoints (taskOrder PythagSysSpec) \<longrightarrow> startPostAssertVC PythagSystem PythagSysSpec PythagTaskContracts (currTidSystemState st2) st1 st2"
    using "tidset" currTid
    apply auto
     apply (simp add: PythagSquaringPost_satisfied_step local.step wf_st)
    by (auto simp add: PythagSysSpec_def mkSysSpec_def getStartPoints_def PythagSystemTaskOrdering_def)
next
  fix st1 st2
  assume wf_st: "wf_SystemState PythagModel PythagSystem st1"
  assume step: "systemStep PythagSystem st1 st2"
  assume inFlow: "currTidSystemState st2 \<in> getAllPoints (taskOrder PythagSysSpec)"
  assume currTid: "tid = currTidSystemState st2"
  from tidInSys have tidset: "tid \<in> {TID_Squaring, TID_TripCheck}"
    by (simp add: Pythag_simps)
  show "currTidSystemState st2 \<notin> getStartPoints (taskOrder PythagSysSpec) \<longrightarrow> taskPostAssertVC PythagSystem PythagSysSpec PythagTaskContracts (currTidSystemState st2) st1 st2"
    using tidset currTid
    apply auto
    apply (simp add: PythagSysSpec_def mkSysSpec_def getStartPoints_def PythagSystemTaskOrdering_def TID_Squaring_def TID_TripCheck_def)      
    by (simp add: PythagTripCheckPost_satisfied_step local.step wf_st)
qed

(* ---------------- Fun Post ------------------ *)

text \<open>Output:
        funPostVC: Triple Check Post-Assertion --> Triple Post-condition\<close>

lemma TriplePostVC: "funPostVC PythagSystem PythagModel PythagSysSpec"
  apply (auto simp add: funPostVC_def)
proof -
  fix st
  assume wf_st: "wf_SystemState PythagModel PythagSystem st"
  assume currTidInendPoints: "currTid (scheduleState st) \<in> getEndPoints (taskOrder PythagSysSpec)"
  assume foldPost: "foldFinalPostAssert PythagSysSpec st" 

  from foldPost have "TripCheck_Pythag_End st"
    by (auto simp add: foldFinalPostAssert_def PythagSysSpec_def mkSysSpec_def getEndPoints_def PythagSystemTaskOrdering_def TID_TripCheck_def TID_Squaring_def Pythag_End_def)

  thus "funPost PythagSysSpec st"
    by (auto simp add: PythagSysSpec_def mkSysSpec_def TripCheck_Pythag_End_def Triple_Pythag_Post_def)
qed
 
(*---------------- ContractConformanceVCs  ---------------- *)

text \<open>Output:
        funPreVC: Pythag System Precondition --> Triple Function Precondition
        startPreVC: Triple Function Precondition --> Squaring Preconditionn
        taskPreVC: Squaring Post-Assertion --> Triple Check Precondition
        startPostAssertVC: Triple Function Precondition --> Squaring Post-Assertion
        taskPostAssertVC: Squaring Post-Assertion --> Triple Check Post-Assertion
        funPostVC: Triple Check Post-Assertion --> Triple Post-condition
        ScheduleContractsVC\<close>

lemma ContractConformance: "ContractConformanceVCs PythagSystem PythagModel PythagTaskContracts PythagSysSpec PythagScheduleContract"
  apply (simp add: ContractConformanceVCs_def)
  by (metis PythagScheduleContracts_wf PythagSubSysSpec_wf PythagTaskContracts_wf Pythag_ScheduleContractsVC 
            TriplePostVC nextTidInSys postVC preVC stepNextTidCurrTid subset_iff taskPostVC_def wf_PythagModel 
            wf_PythagSystem wf_SystemSpec_def wf_SystemSpec_domWRTControlFlow_def wf_SystemSpec_domWRTSchedule_def)
   
end