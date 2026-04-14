theory HAMRMicro04Spec 
  imports HAMRMicro04Model HAMRMicro04ExecutionSemantics SetsAndMaps
begin

(*

TODO:
. assume one pass for vc \<checkmark>
. notes on each vc \<checkmark>
. add example \<checkmark>
. add auxiliary variables to act as a "Log"
. look independence

. fix terminology \<checkmark>

. establish a component that freezes values so every component observes the same value \<checkmark>
  - read all input at one point \<checkmark>
  - then copy the local vars \<checkmark>
  - eventually use sequences \<checkmark>

. add a structure into a hierarchy of
  - TaskOrdering Contracts \<checkmark>
  - Atomic systems contracts
    - Should contain all task ordering contracts for an atomic system
  - System with systems contracts
    - Prove the correlation between systems with snapshotting of the sub-system post conditions

. Fix the diagram make vcs and ordering more explicit
  - Petri net

. Refinement Systematically
   - can be used to discuss how much easier it is

. Remove smt solver

. 
*)

section \<open>Data Structures\<close>

type_synonym ('a, 'b) CRel = "'a \<Rightarrow> 'b \<Rightarrow> bool"

fun mkCRel :: "('a * 'b) set \<Rightarrow> ('a, 'b) CRel"
  where "mkCRel S = (\<lambda> a. \<lambda> b . (a, b) \<in> S)"

fun empCRel where "empCRel x y = False" 

fun domCRel :: "('a, 'b) CRel => 'a set"
  where "domCRel r = {a . \<exists>b. r a b}"

fun ranCRel :: "('a, 'b) CRel => 'b set"
  where "ranCRel r = {b . \<exists>a. r a b}"

section \<open>Specifications\<close>

subsection \<open>Specification Category: ScheduleContracts Specifications\<close>

type_synonym ScheduleMayFollow = "(Tid,Tid) CRel"

record ScheduleContracts =
  mayFollow :: "ScheduleMayFollow"

fun mkScheduleContracts :: 
   "ScheduleMayFollow \<Rightarrow> ScheduleContracts"
  where "mkScheduleContracts mf = 
           \<lparr>mayFollow = mf\<rparr>"

definition wf_ScheduleContracts :: "'store System \<Rightarrow> ScheduleContracts \<Rightarrow> bool"
  where "wf_ScheduleContracts sys scs 
           \<equiv> \<forall>tid1 tid2 . (mayFollow scs) tid1 tid2 \<longrightarrow> 
                tid1 \<in> systemTids sys \<union> {initTid} 
             \<and>  tid2 \<in> systemTids sys"

subsection \<open>Specification Category: Flow Specifications\<close>

type_synonym TaskOrdering = "(Tid,Tid) CRel"

(* Get all tids following a specific tid in the task ordering *)

definition getTidFollow :: "TaskOrdering \<Rightarrow> Tid \<Rightarrow> Tid set"
  where "getTidFollow to tid \<equiv> {t | t. to tid t }"

(* Get all tids preceding a specific tid *)

definition getTidPreceed :: "TaskOrdering \<Rightarrow> Tid \<Rightarrow> Tid set"
  where "getTidPreceed to tid \<equiv> {t | t. to t tid }"

(* Get all tids in the ordering by unioning the dom and ran*)

definition getAllPoints :: "TaskOrdering \<Rightarrow> Tid set"
  where "getAllPoints to \<equiv> domCRel to \<union> ranCRel to"

(* Get all tids at the start of the flow by subtracting the dom from the ran which should
   give all points at the start of the flow because it should be points that don't follow anything 
   since it is not in the range *)

definition getStartPoints :: "TaskOrdering \<Rightarrow> Tid set"
  where "getStartPoints to \<equiv> domCRel to - ranCRel to"

(* Get all tids at the end of the flow by subtracting the ran from the dom which should
   give all points at the end of the flow because it should be points that don't precede anything 
   since it is not in the domain *)

definition getEndPoints :: "TaskOrdering \<Rightarrow> Tid set"
  where "getEndPoints to \<equiv> ranCRel to - domCRel to"

named_theorems TaskOrdering_simps
lemmas [TaskOrdering_simps] =
  getTidFollow_def
  getTidPreceed_def
  getAllPoints_def
  getStartPoints_def
  getEndPoints_def

subsubsection \<open>Task Order  Well-Formedness\<close>

(* The number of points at the start of the flow should be more than 1 *)

definition wf_TaskOrdering_wfStart :: "TaskOrdering \<Rightarrow> bool"
  where "wf_TaskOrdering_wfStart to \<equiv> card (getStartPoints to) \<ge> 1"

(* The number of points at the end of the flow should be more than 1 *)

definition wf_TaskOrdering_wfEnd :: "TaskOrdering \<Rightarrow> bool"
  where "wf_TaskOrdering_wfEnd to \<equiv> card (getEndPoints to) \<ge> 1"

(* The task ordering should be finite *)

definition wf_TaskOrdering_FiniteOrdering :: "TaskOrdering \<Rightarrow> bool"
  where "wf_TaskOrdering_FiniteOrdering to \<equiv> finite (getAllPoints to)"

(* if b follows a in the task ordering then b should follow a in the schedule contract *)

definition wf_TaskOrdering_ScheduleContractConformence :: "ScheduleContracts \<Rightarrow> TaskOrdering \<Rightarrow> bool"
  where "wf_TaskOrdering_ScheduleContractConformence sc to \<equiv> \<forall>a. \<forall>b. to a b \<longrightarrow> (mayFollow sc) a b"

definition wf_TaskOrdering :: "ScheduleContracts \<Rightarrow> TaskOrdering \<Rightarrow> bool"
  where "wf_TaskOrdering sc to \<equiv> 
          wf_TaskOrdering_FiniteOrdering to
          \<and> wf_TaskOrdering_ScheduleContractConformence sc to
          \<and> wf_TaskOrdering_wfEnd to
          \<and> wf_TaskOrdering_wfStart to"

named_theorems wf_Flow_simps
lemmas [wf_Flow_simps] =
  wf_TaskOrdering_wfEnd_def
  wf_TaskOrdering_FiniteOrdering_def
  wf_TaskOrdering_wfStart_def
  wf_TaskOrdering_ScheduleContractConformence_def
  wf_TaskOrdering_def
  

subsection \<open>Specification category: Task Specifications\<close>

text \<open>Same as HAMRMicro2 with addition of splitting store into TaskState and ChState\<close>

type_synonym 'value InitPost = "'value TaskState \<Rightarrow> 'value ChState \<Rightarrow> bool"
type_synonym 'value TaskPre = "'value TaskState \<Rightarrow> 'value ChState \<Rightarrow> bool"
type_synonym 'value TaskPost = "'value TaskState \<Rightarrow> 'value ChState \<Rightarrow> 'value TaskState \<Rightarrow> 'value ChState \<Rightarrow> bool"

record 'value TaskContracts =
  initPost :: "'value InitPost" (* Contract for start state *)
  taskPre :: "(Tid, 'value TaskPre) map" (* Task pre condition *)
  taskPost :: "(Tid, 'value TaskPost) map"   (* Task post-condition *)

fun mkTaskContracts :: 
   "'value InitPost \<Rightarrow> (Tid, 'value TaskPre) map 
                    \<Rightarrow> (Tid, 'value TaskPost) map \<Rightarrow> 'value TaskContracts"
  where "mkTaskContracts ipost preMap postMap = 
           \<lparr>initPost = ipost, taskPre = preMap, taskPost = postMap\<rparr>"

definition wf_TaskContracts :: "'store System \<Rightarrow> 'store TaskContracts \<Rightarrow> bool"
  where "wf_TaskContracts sys tcs = ((systemTids sys) = dom (taskPre tcs)
                                   \<and> (systemTids sys) = dom (taskPost tcs))"

subsection \<open>Specification category: System Specifications\<close>

type_synonym 'value SystemAssert = "'value SystemState \<Rightarrow> bool"

(* 
For a given subsystem we want to specify the behavior of an abstract function of an output port
we want to specify this in terms of the subsystem precondition, the abstract function precondition,
the system assertion for each tasks, and the abstract function post condition.
*)

record 'value SystemSpec = 
  taskOrder :: "TaskOrdering"
  sysPre :: "'value SystemAssert"
  funPre :: "'value SystemAssert"
  sysTasksAsserts :: "(Tid, 'value SystemAssert) map"
  funPost :: "'value SystemAssert"

definition mkSysSpec :: "TaskOrdering \<Rightarrow> 'value SystemAssert \<Rightarrow> 'value SystemAssert \<Rightarrow> (Tid, 'value SystemAssert) map \<Rightarrow> 'value SystemAssert \<Rightarrow> 'value SystemSpec"
  where "mkSysSpec to sp fpre sta fpost \<equiv> \<lparr>taskOrder = to, sysPre = sp, funPre = fpre, sysTasksAsserts = sta, funPost = fpost \<rparr>"

(* All task assertions should be for scheduled tasks*)

definition wf_SystemSpec_domWRTSchedule :: "'value SystemSpec \<Rightarrow> 'value System \<Rightarrow> bool"
  where "wf_SystemSpec_domWRTSchedule sysSpec sys \<equiv>  dom (sysTasksAsserts sysSpec) \<subseteq> set (schedule sys)"

(* Every point in the task ordering should have a post-assertion *)

definition wf_SystemSpec_domWRTControlFlow :: "'value SystemSpec \<Rightarrow> TaskOrdering \<Rightarrow> bool"
  where "wf_SystemSpec_domWRTControlFlow sysSpec to \<equiv> dom (sysTasksAsserts sysSpec) = (getAllPoints to)"

definition wf_SystemSpec ::  "'value SystemSpec \<Rightarrow> 'value System \<Rightarrow> ScheduleContracts \<Rightarrow> bool"
  where "wf_SystemSpec sysSpec sys sc \<equiv>
          wf_SystemSpec_domWRTSchedule sysSpec sys
          \<and> wf_SystemSpec_domWRTControlFlow sysSpec (taskOrder sysSpec)
          \<and> wf_TaskOrdering sc (taskOrder sysSpec)"

named_theorems wf_SystemSpec_simps
lemmas [wf_SystemSpec_simps] =
  wf_SystemSpec_domWRTSchedule_def
  wf_SystemSpec_domWRTControlFlow_def
  wf_SystemSpec_def
  wf_Flow_simps

subsubsection \<open>Verification Condition\<close>

(* -------- V C s   H e l p e r   F u n c t i o n s -------- *)

text \<open>Conjoin all previous tasks post assertions\<close>

definition foldPostAssert :: "'value SystemSpec \<Rightarrow> 'value SystemState \<Rightarrow> Tid \<Rightarrow> bool"
  where "foldPostAssert sysSpec st nextTid = 
         Finite_Set.fold (\<lambda>a b. a \<and> b) True {((sysTasksAsserts sysSpec) $ t) st | t. (taskOrder sysSpec) t nextTid}"


text \<open>Fold all preconditions at the end of the a subsystem\<close>

definition foldFinalPostAssert :: "'value SystemSpec \<Rightarrow> 'value SystemState \<Rightarrow> bool"
  where "foldFinalPostAssert sysSpec st = 
         Finite_Set.fold (\<lambda>a b. a \<and> b) True {((sysTasksAsserts sysSpec) $ t) st | t. t \<in> getEndPoints (taskOrder sysSpec)}"

(* -------- S c h e d u l e   C o n t r a c t    V C s --------------*)

text \<open>In a scheduling state that just executed currTid, the next scheduled
task currTid' is in the mayFollow scheduling contract.\<close>

definition ScheduleContractsVC 
  :: "'store System \<Rightarrow> Model \<Rightarrow> ScheduleContracts \<Rightarrow> bool" 
  where "ScheduleContractsVC sys m schcons \<equiv> 
   wf_System sys m \<and> wf_ScheduleContracts sys schcons \<longrightarrow>
   (\<forall>schst .
    wf_ScheduleState sys schst
   \<longrightarrow> (mayFollow schcons) (currTid schst) (currTid (scheduleNext (schedule sys) schst)))"

(* -------- P r e   C o n d i t i o n      V C s --------------*)

(* Will account for this later when we are not doing one pass over the system only *)

(*
text \<open>Precondition of the Component\<close>

definition subsysPreVC :: "'value System \<Rightarrow> 'value SystemSpec \<Rightarrow> 'value SystemState \<Rightarrow> bool"
  where "subsysPreVC sys sysSpec st \<equiv> (subsysPre sysSpec) st"
*)

text \<open>Precondition of the System --> Function precondition\<close>

(*
This VC is that the precondition of the subsystem must imply the precondition of the abstract function​
*)

definition funPreVC :: "'value System \<Rightarrow> 'value SystemSpec \<Rightarrow> 'value SystemState \<Rightarrow> bool"
  where "funPreVC sys sysSpec st \<equiv> (sysPre sysSpec) st \<longrightarrow> (funPre sysSpec) st"

text \<open>Function precondition --> Precondition of all tasks that can come first\<close>

(*
This VC is that the precondition of the abstract function must imply the precondition of all tasks
that can be scheduled first for the subsystem​
*)

definition startPreVC :: "'value System \<Rightarrow> 'value SystemSpec \<Rightarrow> 'value TaskContracts \<Rightarrow> 'value SystemState \<Rightarrow> Tid \<Rightarrow> bool"
  where "startPreVC sys sysSpec con st nextTid \<equiv> 
        (funPre sysSpec) st \<longrightarrow> ((taskPre con) $ nextTid) ((systemTasks st) $ nextTid) (systemChs st)"

(*
This VC is that the conjunction of all preceding tasks post assertions implies the precondition of
the current task​
*)

definition taskPreSysVC :: "'value System \<Rightarrow> 'value SystemSpec \<Rightarrow> 'value TaskContracts \<Rightarrow> 'value SystemState \<Rightarrow> Tid \<Rightarrow> bool"
  where "taskPreSysVC sys sysSpec con st nextTid \<equiv> 
          foldPostAssert sysSpec st nextTid \<longrightarrow> ((taskPre con) $ nextTid) ((systemTasks st) $ nextTid) (systemChs st)"

(* 
For a given state, if the state directly precedes a tasks that can be scheduled first for a subsystem,
then the state should satisfy startPreVC and funPreVC, else, it should satisfy taskPreSysVC

We use mayFollow instead of Task Order here so that the state can refer to state that does not belong to
any task in the Task Order
*)

definition taskPreVC :: "'value System \<Rightarrow> Model \<Rightarrow> ScheduleContracts \<Rightarrow> 'value TaskContracts \<Rightarrow> 'value SystemSpec \<Rightarrow> Tid \<Rightarrow> bool"
  where "taskPreVC sys m schons cons sysSpec nextTid \<equiv> 
          (\<forall>st . 
             (wf_SystemState m sys st 
            \<and> ((mayFollow schons) (currTidSystemState st) nextTid)
            \<and> nextTid \<in> getAllPoints (taskOrder sysSpec))
            \<longrightarrow> (((nextTid \<in> getStartPoints (taskOrder sysSpec))
                    \<longrightarrow> startPreVC sys sysSpec cons st nextTid
                        \<and> funPreVC sys sysSpec st)
               \<and> ((nextTid \<notin> getStartPoints (taskOrder sysSpec))
                   \<longrightarrow> taskPreSysVC sys sysSpec cons st nextTid))
           )"

(* -------- P o s t - c o n d i t i o n    V C s --------------*) 

text \<open>All post asserts of the current state --> The post assert of the next state\<close>

(* 
This VC is that the conjunction of all preceding tasks post assertions implies the post-assertion
of the current task​
*)


definition taskPostAssertVC :: "'value System \<Rightarrow> 'value SystemSpec \<Rightarrow> 'value TaskContracts \<Rightarrow> Tid \<Rightarrow> 'value SystemState \<Rightarrow> 'value SystemState \<Rightarrow> bool"
  where "taskPostAssertVC sys sysSpec con nextTid st1 st2 \<equiv> foldPostAssert sysSpec st1 nextTid \<longrightarrow> ((sysTasksAsserts sysSpec) $ nextTid) st2"

(*
This VC is that the precondition of the abstract function must imply the post-assertion of all tasks
that can be scheduled first for the subsystem​
*)

definition startPostAssertVC :: "'value System \<Rightarrow> 'value SystemSpec \<Rightarrow> 'value TaskContracts \<Rightarrow> Tid \<Rightarrow> 'value SystemState \<Rightarrow> 'value SystemState \<Rightarrow> bool"
  where "startPostAssertVC sys sysSpec con nextTid st1 st2 \<equiv> (funPre sysSpec) st1 \<longrightarrow> ((sysTasksAsserts sysSpec) $ nextTid) st2"

(* 
If a tasks that can precede any other tasks in a subsystem is executed, then the original state and 
the resulting state state should satisfy startPostAssertVC, else, it should satisfy taskPostAssertVC
*)

definition taskPostVC :: "'value System \<Rightarrow> Model \<Rightarrow> 'value TaskContracts \<Rightarrow> 'value SystemSpec \<Rightarrow> Tid \<Rightarrow> bool"
  where "taskPostVC sys m cons sysSpec tid \<equiv>
          (\<forall>st1 st2. (wf_SystemState m sys st1 
                   \<and> systemStep sys st1 st2
                   \<and> tid = (currTidSystemState st2)
                   \<and> tid \<in> getAllPoints (taskOrder sysSpec))
             \<longrightarrow> (((tid \<in> getStartPoints (taskOrder sysSpec))
                    \<longrightarrow> (startPostAssertVC sys sysSpec cons tid st1 st2))
                  \<and> ((tid \<notin> getStartPoints (taskOrder sysSpec)) 
                    \<longrightarrow> (taskPostAssertVC sys sysSpec cons tid st1 st2))))"

(*
This VC is that the conjunction of all end tasks post assertions implies the abstract function post-condition​
*)

definition funPostVC :: "'value System \<Rightarrow> Model \<Rightarrow> 'value SystemSpec \<Rightarrow> bool"
  where "funPostVC sys m sysSpec \<equiv>
          (\<forall> st. (wf_SystemState m sys st
               \<and> currTidSystemState st \<in> getEndPoints (taskOrder sysSpec))
            \<longrightarrow> (foldFinalPostAssert sysSpec st \<longrightarrow> (funPost sysSpec) st))"

(* -------- C o m b i n e d      V C s --------------*)

definition ContractConformanceVCs :: "'value System \<Rightarrow> Model \<Rightarrow> 'value TaskContracts \<Rightarrow> 'value SystemSpec \<Rightarrow> ScheduleContracts \<Rightarrow> bool"
  where "ContractConformanceVCs sys m cons sysSpec schons \<equiv> (
          wf_TaskContracts sys cons
          \<and> wf_ScheduleContracts sys schons
          \<and> wf_SystemSpec sysSpec sys schons
          \<and> ScheduleContractsVC sys m schons
          \<and> (\<forall>tid \<in> (getAllPoints (taskOrder sysSpec)). taskPreVC sys m schons cons sysSpec tid))
          \<and> (\<forall>tid \<in> (getAllPoints (taskOrder sysSpec)). taskPostVC sys m cons sysSpec tid)
          \<and> funPostVC sys m sysSpec"

section \<open>Soundness\<close>

(* TODO Later*)

end