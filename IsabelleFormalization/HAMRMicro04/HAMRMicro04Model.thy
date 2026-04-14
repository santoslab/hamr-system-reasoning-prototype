theory HAMRMicro04Model 
  imports Main SetsAndMaps
begin

section \<open>Model Representation (Static Structure)\<close>

subsection \<open>Identifiers\<close>

text \<open>Tasks correspond to HAMR's thread components.  
They are atomically executing, statically scheduled actions that
write and read to/from a global communication substrate and that
update a task-local collection of variables.\<close>

text \<open>Define a type of task identifiers.\<close>

type_synonym Tid = nat

type_synonym Tids = "Tid set"

text \<open>For now use "0" as the ID of the "AADL initialization phase".  
We do not represent the execution of the initialization phase in this sketch
model.  Instead, we represent the "outcome" of the phase with an invariant/contract
on the store in the initial system state.   The system state includes the Tid of the 
task whose execution just completed.   To support a uniform representation of 
"the Tid of the task just completed" -- even in the initialization state, we 
introduce @{term initTid} along with specifications that it is disjoint from the 
set of Tids of the tasks actually declared in the system.\<close>

definition initTid :: "Tid"
  where "initTid \<equiv> (0 :: nat)"

text \<open>As in HAMR, a task's variable identifiers are represented as strings.\<close>

type_synonym VarId = "string"
type_synonym VarIds = "VarId set"

text \<open>Below we define the notion of a channel identifier.  
There is no direct correspondence in HAMR. Indirectly, channels
in this sketch simplify and unify the notions of HAMR ports and 
the global communication substrate.  The aim is to expose concepts
of constrained interaction between tasks (instead of interacting
via arbitrary global variables as in previous HAMR Micro sketches
(i.e., any task could ready any global variable), in this sketch 
tasks will only be allowed to read/write specific inputs and outputs
(channels) as declared in task descriptors.  This allows us to 
move toward a notion of contract in this sketch that matches the 
structure of GUMBO contracts: constraints on task inputs and outputs
with optional evolution of task-local variables.

Note: one potential weakness with this sketch strategy is that 
it makes the definition and well-formedness of tasks slightly 
non-local or non-compositional: a task doesn't just reference 
local entities like HAMR threads (local vars, local ports), it
instead references the global channels.  This will make notions
of task well-formedness slightly less modular.
\<close>


type_synonym ChId = string
type_synonym ChIds = "ChId set"

text \<open>
A task descriptor defines a "schema" for a task's state and functionality.
It indicates what global channels the task is allowed to read and write,
as well as the domain of its local variable state. 

The task descriptor is a simplification of HAMR's CompDescr (see HAMR Model.thy).
\<close>

record TaskDescr =
  inChIds :: "ChIds" (* task can read input channels *)
  outChIds :: "ChIds" (* task can write output channels *)
  varIds :: "VarIds" (* task can read/write local variables *)


text \<open>A task's input and output channel ids must be disjoint.\<close>

definition wf_TaskDescr_InputOutputIDsDisjoint :: "TaskDescr \<Rightarrow> bool"
  where "wf_TaskDescr_InputOutputIDsDisjoint tdescr 
         \<equiv> (inChIds tdescr) \<inter> (outChIds tdescr) = {}"

text \<open>A task's channel ids must belong to the set of the system-wide
      declared channel ids (this set is supplied as an argument).\<close>

definition wf_TaskDescr_IOIDsSubsetOfChIDs :: "TaskDescr \<Rightarrow> ChIds \<Rightarrow> bool"
  where "wf_TaskDescr_IOIDsSubsetOfChIDs tdescr chIds 
         \<equiv> (inChIds tdescr) \<subseteq> chIds \<and> (outChIds tdescr) \<subseteq> chIds"

text \<open>Well-formedness for a task descriptor is the conjunction of the properties above.\<close>

definition wf_TaskDescr :: "TaskDescr \<Rightarrow> ChIds \<Rightarrow> bool"
  where "wf_TaskDescr tdescr chIds \<equiv>  wf_TaskDescr_InputOutputIDsDisjoint tdescr 
                                      \<and> wf_TaskDescr_IOIDsSubsetOfChIDs tdescr chIds"

named_theorems wf_TaskDescrs_simps
lemmas [wf_TaskDescrs_simps] =
  wf_TaskDescr_InputOutputIDsDisjoint_def
  wf_TaskDescr_IOIDsSubsetOfChIDs_def
  wf_TaskDescr_def

text \<open>The following function can be used to abbreviate the declaration of 
component descriptors.\<close>

fun mkTaskDescr where "mkTaskDescr ins outs vs = 
  \<lparr> inChIds=ins,  outChIds=outs, varIds =vs \<rparr>"

text \<open>
A system (model) description includes its channel identifiers,
and table associating its task identifiers to task
descriptors.  We have decided to use "Model" as the name of this structure
since that corresponds to the HAMR "Model" definition in
Model.thy\<close>

record Model =
  modelTaskDescrs :: "(Tid, TaskDescr) map"  
  modelChIds :: "ChIds"

text \<open>Helper function to return the component identifiers in model m (similar to modelCIDs 
in HAMR Model.thy).\<close>

fun modelTids:: "Model \<Rightarrow> Tids"
  where "modelTids m = dom (modelTaskDescrs m)"

text \<open>In a well-formed model, the distinct initTid representing the HAMR initialization phase
must not be used as an identifier for an application Tid.\<close>

definition wf_Model_Tids :: "Model \<Rightarrow> bool"
  where "wf_Model_Tids m \<equiv> initTid \<notin> modelTids m"

text \<open>In a well-formed model, all task descriptors are well-formed.\<close>

definition wf_Model_TaskDescrs :: "Model \<Rightarrow> bool"
  where "wf_Model_TaskDescrs m \<equiv>
          \<forall>tid \<in> dom (modelTaskDescrs m). 
            wf_TaskDescr ((modelTaskDescrs m) $ tid) (modelChIds m)"

text \<open>The following well-formedness property is similar to the AADL restriction that
there is no fan-in for data ports.
Each channel id chId that is used as an input channel for a particular task tid
 (1) has a unique task tid' in which chId appears as an output, or 
 (2) has no task that provides an input.\<close>

definition wf_Model_InHasUniqueOut :: "Model \<Rightarrow> bool"
  where "wf_Model_InHasUniqueOut m \<equiv> 
          \<forall>tid \<in> dom (modelTaskDescrs m).
           \<forall>chId \<in> (inChIds ((modelTaskDescrs m) $ tid)).
           \<comment> \<open>Case 1: There exists a unique task tid' that has chId as output.\<close>
            (\<exists>tid' \<in> dom (modelTaskDescrs m). \<comment> \<open>There exists a task tid' that has chId as output\<close>
                chId \<in> (outChIds ((modelTaskDescrs m) $ tid')) 
             \<and> (\<forall>tid'' \<in> dom (modelTaskDescrs m). 
                    \<comment> \<open>For every task tid'' that has chId as an output, that task 
                        is actually tid' (i.e., the sending task is unique).\<close>
                   (chId \<in> (outChIds ((modelTaskDescrs m) $ tid''))) \<longrightarrow> tid' = tid''))
           \<comment> \<open>Case 2: There does not exist a task tid' that has chId as an output.\<close>
         \<or>  \<not>(\<exists>tid' \<in> dom (modelTaskDescrs m). 
                       chId \<in> (outChIds ((modelTaskDescrs m) $ tid')))"

definition wf_Model :: "Model \<Rightarrow> bool"
  where "wf_Model m \<equiv> wf_Model_TaskDescrs m \<and> wf_Model_Tids m \<and> wf_Model_InHasUniqueOut m"
                      

named_theorems wf_Model_simps
lemmas [wf_Model_simps] =
  wf_Model_TaskDescrs_def
  wf_Model_Tids_def
  wf_Model_InHasUniqueOut_def
  wf_Model_def

section \<open>State Structure\<close>

subsection \<open>Var State\<close>

text \<open>A @{term VarState} is used to represent the state of 
a task's local variables whose value persist between task dispatches.
Each task has its own @{term VarState} structure as part of its state.
This matches HAMR's notion of VarState (See HAMR VarState.thy).

A @{term VarState} is a map, associating a var id with
  a value of type 'a, representing the value of the variable.
The notion of application variable type and value is not fully
developed at this point, so we parameterize the @{term VarState}
of a type \emph{a} representing a universal value type.\<close>

type_synonym 'a VarState = "(VarId, 'a) map"

text \<open>We will need to enforce a model/state well-formedness condition
that states that the var state domain of a task matches the VarId set
in its descriptor.  Use the definition below to support that
(these correspond to definitions in HAMR VarState.thy).\<close>

definition wf_VarState_dom :: "VarIds \<Rightarrow> 'a VarState \<Rightarrow> bool" where 
  "wf_VarState_dom vids vs \<equiv> (dom vs) = vids"

subsection \<open>Task State\<close>

text \<open>A task state is a (dramatic) simplification of the HAMR thread state 
(see HAMR ThreadState.thy). Currently, a task's state only 
includes a @{term VarState} (it omits HAMR thread states notions of port
state because this HAMR micro sketch has tasks interacting directly 
with the global communication substrate represented as channels (thus, 
the AADL RT concepts like ReceiveInput and SendOutput are bypassed in 
this sketch).\<close>

record 'a TaskState =
  tvar :: "'a VarState"

text \<open>The following function helps abbreviate the construction of a task state.\<close>

fun tstate where "tstate tv = 
 \<lparr> tvar = tv \<rparr>"

text \<open>
A task state conforms to its descriptor when the domain of its
variable state matches the declared var ids in its descriptor. 
\<close>

definition wf_TaskState :: "TaskDescr \<Rightarrow> 'a TaskState \<Rightarrow> bool"
  where "wf_TaskState td ts \<equiv>  wf_VarState_dom (varIds td) (tvar ts)"
          

subsection \<open>Channel State\<close>

text \<open>Channels are part of the global system state. 
Each channel holds a single value that can be written
by components having write access to the channel and
read by components having read access to the channel.\<close>

type_synonym 'a ChState = "(ChId, 'a) map"

definition wf_ChState :: "ChIds \<Rightarrow> 'a ChState  \<Rightarrow> bool" where 
  "wf_ChState chids cs \<equiv> (dom cs) = chids"

subsection \<open>Schedule\<close>

text \<open>This sketch model adopts a static cyclic scheduling approach that is very
similar to what is used in the HAMR seL4 representation.  The schedule is a list
of slots (represented as Isabelle list entries) where each slot holds a Tid.
The complete list represents a single cycle (major frame) in the scheduling
behavior.  Each task tid can appear more than one time in the schedule.

The schedule must always have at least one entry.  This will be enforced by
well-formedness conditions.\<close>

type_synonym Schedule = "Tid list" 

subsection \<open>Schedule State (Dynamic/runtime data structure)\<close>

type_synonym SlotNum = nat

definition initSlotNum :: "SlotNum"
  where [simp add]: "initSlotNum \<equiv> (0 :: nat)"

record ScheduleState =
  currTid :: Tid \<comment> \<open>The task that was executed to get to this state.\<close> 
  nextSlotNum :: SlotNum \<comment> \<open>0-based index of the next slot in the schedule to be executed.\<close>

text \<open>Helper Functions for Schedule State\<close>

fun mkScheduleState :: "Tid \<Rightarrow> SlotNum \<Rightarrow> ScheduleState"
  where "mkScheduleState tid slotNum = \<lparr>currTid = tid, nextSlotNum = slotNum\<rparr>"

fun initScheduleState :: "Schedule \<Rightarrow> ScheduleState"
  where "initScheduleState sched = mkScheduleState initTid initSlotNum"

text \<open>Advance the slot number one position, and wrap around (using 0-based indexing)\<close>

fun computeNextSlotNum :: "Schedule \<Rightarrow> SlotNum \<Rightarrow> SlotNum"
  where "computeNextSlotNum sch slotNum = 
           (if (slotNum < length sch - 1) 
            then slotNum + 1
            else 0)"

text \<open>Move back the slot number one position, and wrap around (using 0-based indexing)\<close>
fun computePrevSlotNum :: "Schedule \<Rightarrow> SlotNum \<Rightarrow> SlotNum"
  where "computePrevSlotNum sch slotNum = 
           (if (slotNum > 0)
            then slotNum - 1
            else (length sch) - 1)"

text \<open>Fetch the task identifier at the given slot number from the schedule.\<close>

fun fetchTidFromSlot :: "Schedule \<Rightarrow> SlotNum \<Rightarrow> Tid" where
 "fetchTidFromSlot sch slotNum = nth sch slotNum"

text \<open>The @{term scheduleNext} function below implements the
main scheduling steps: (a) retrieving the determine the Tid of the next task to execute
from the next slot in the static schedule, and (b) advancing the nextSlotNum index.\<close>

fun scheduleNext :: "Schedule \<Rightarrow> ScheduleState \<Rightarrow> ScheduleState"
  where 
    "scheduleNext sch schst = 
      mkScheduleState (fetchTidFromSlot sch (nextSlotNum schst))
                      (computeNextSlotNum sch (nextSlotNum schst))"

definition scheduleStep :: "Schedule \<Rightarrow> ScheduleState \<Rightarrow> ScheduleState \<Rightarrow> bool"
  where "scheduleStep sch schst1 schst2 \<equiv> (scheduleNext sch schst1 = schst2)"

definition scheduleReach :: "Schedule \<Rightarrow> ScheduleState \<Rightarrow> bool" where 
 "scheduleReach sch schst = ((scheduleStep sch)\<^sup>*\<^sup>* (initScheduleState sch) schst)"

text \<open>Well Formedness Properties for schedule state is stated lower in the file\<close>

subsection \<open>System State\<close>

text \<open>A system state consists of the channel state and task
state for each task in the system.  This is a simplification
of HAMR's system state (see HAMR SystemState.thy) that includes
a states for each thread and the state of the communication substrate.\<close>

record 'a SystemState =
  systemTasks :: "(Tid, 'a TaskState) map" \<comment> \<open>states of each task\<close>
  systemChs :: "'a ChState" \<comment> \<open>state of communication substrate\<close>
  scheduleState :: ScheduleState
  previousSystemTasks :: "(Tid, 'a TaskState) map"
  previousSystemChs :: "'a ChState"

subsection \<open>Task Behaviors\<close>

text \<open>Each task's behavior is an action that updates the global 
channel state (representing outputs of the component) as well as the 
local var state for a component.\<close>

type_synonym 'value Action = 
  "('value TaskState \<times> 'value ChState) \<Rightarrow> ('value TaskState \<times> 'value ChState)"

text \<open>Each task has an unique identifier and an "action", corresponding to 
developer-written application code, that updates system variables.\<close>

record 'value Task =
  taskId :: Tid
  action :: "'value Action"

fun mkTask :: "Tid \<Rightarrow> 'value Action \<Rightarrow> 'value Task"
  where "mkTask i a = \<lparr>taskId = i, action = a\<rparr>"


text \<open>The system representation includes a data structure mapping task identiers
to tasks.\<close>

type_synonym 'value TaskMap = "(Tid, 'value Task) map"

text \<open>A system specification includes an initial store, a data structure holding
all the task specifications and a specification of the static schedule.\<close>

record 'value System =
  initSystemState :: "'value SystemState"
  taskMap :: "'value TaskMap"
  schedule :: Schedule

text \<open>A system schedule is well-formed when (a) all task ids in the schedule are
declared in the system task map and (b) when the schedule contains at least one task.
\<close>

definition wf_System_Schedule :: "'value System \<Rightarrow> bool"
  where "wf_System_Schedule sys \<equiv>
    (\<forall>tid \<in> (set (schedule sys)). tid \<in> dom (taskMap sys)) \<and> length (schedule sys) > 0"

text \<open>The set of task ids for which we have defined actions (i.e., the domain of the taskMap),
matches the ids of the tasks declared in the model.\<close>

definition wf_System_TidsDom :: "'value System \<Rightarrow> Model \<Rightarrow> bool"
  where "wf_System_TidsDom sys m \<equiv> dom (taskMap sys) = modelTids m"

text \<open>The @{term initTid} must not appear in the IDs used in the task map.
Note that if the task map domain matches the modelTids, this property 
follows since we already require that @{term initTid} not appear in the 
modelTids.\<close>
definition wf_System_Tids :: "'store System \<Rightarrow> bool"
  where "wf_System_Tids sys \<equiv> (initTid \<notin>  dom (taskMap sys))"

(* NOTE: For the definitions below, we should consider the possible use of 
   pair patterns and let bindings to introduce temporary names that the make
   the definitions more readable. *)

\<comment> \<open>System actions preserve the well-formedness of channel states, i.e., 
    for all task actions,
     for all task inputs (ts, cs)
      if the input channel state cs is well-formed,
       then the output channel state that results from running the action is well-formed. \<close>

definition wf_System_ActionsChState :: "'value System \<Rightarrow> Model \<Rightarrow> bool"
  where "wf_System_ActionsChState sys m \<equiv>
          \<comment> \<open>For all tasks tid in the system..\<close>
          \<forall>tid \<in> (dom (taskMap sys)). 
           \<comment> \<open>For all possible action inputs\<close>
           \<forall>(tscs :: ('value TaskState \<times> 'value ChState)). 
           \<comment> \<open>If the channel state is well-formed wrt the model-declared channel ids..\<close>
            wf_ChState (modelChIds m) (snd tscs) \<longrightarrow> 
           \<comment> \<open>..then the channel state produced by the action is well-formed wrt the model-declared channel ids.\<close>
            wf_ChState (modelChIds m) (snd ((action ((taskMap sys) $ tid)) tscs))"

\<comment> \<open>System actions preserve the well-formedness of task states, i.e., 
    for all task actions,
     for all task inputs (ts, cs)
      if the input task state ts is well-formed wrt the model,
       then the output task state that results from running the action is well-formed.\<close>

definition wf_System_ActionsTaskState :: "'value System \<Rightarrow> Model \<Rightarrow> bool"
  where "wf_System_ActionsTaskState sys m \<equiv>
          \<comment> \<open>For all tasks tid in the system..\<close>
          \<forall>tid \<in> (dom (taskMap sys)). 
           \<comment> \<open>For all possible action inputs\<close>
           \<forall>(tscs :: ('value TaskState \<times> 'value ChState)). 
             \<comment> \<open>If the task state ts is well-formed wrt the model-declared task descriptor...\<close>
             wf_TaskState ((modelTaskDescrs m) $ tid) (fst tscs) \<longrightarrow>  
             \<comment> \<open>..then the task state produced by the action is well-formed 
                 wrt the model-declared task descriptor.\<close>
             wf_TaskState ((modelTaskDescrs m) $ tid) 
                          (fst ((action ((taskMap sys) $ tid)) tscs))"


definition wf_System :: "'value System \<Rightarrow> Model \<Rightarrow> bool" 
  where "wf_System sys m \<equiv> wf_System_Schedule sys \<and> 
                           wf_System_Tids sys \<and> 
                           wf_System_ActionsChState sys m \<and>
                           wf_System_ActionsTaskState sys m \<and> 
                           wf_System_TidsDom sys m"

named_theorems wf_System_simps
lemmas [wf_System_simps] =
  wf_System_Schedule_def
  wf_System_Tids_def
  wf_System_def
  wf_System_ActionsChState_def
  wf_System_ActionsTaskState_def
  wf_System_TidsDom_def


fun mkSystem :: "'value SystemState \<Rightarrow> 'value TaskMap \<Rightarrow> Schedule \<Rightarrow> 'value System"
  where "mkSystem init tm sched 
           = \<lparr>initSystemState = init, taskMap = tm, schedule = sched\<rparr>"

text \<open>We interpret the domain of the task map as specifying the set of task identifiers
used in the system.\<close>

text \<open>Jacob. Consider moving this definition up so that all the associated 
well-formedness properties can use it.\<close>

fun systemTids :: "'store System \<Rightarrow> Tids"
  where "systemTids sys = dom (taskMap sys)"

subsection \<open>SystemState Helper Functions\<close>

definition mkSystemState :: "(Tid, 'a TaskState) map \<Rightarrow> 'a ChState \<Rightarrow> ScheduleState \<Rightarrow> (Tid, 'a TaskState) map \<Rightarrow> 'a ChState \<Rightarrow> 'a SystemState"
  where "mkSystemState sysT sysC schedState prevSysT prevSysC = 
           \<lparr>systemTasks = sysT, systemChs = sysC, scheduleState = schedState, previousSystemTasks = prevSysT, previousSystemChs = prevSysC\<rparr>"

fun currTidSystemState :: "'a SystemState \<Rightarrow> Tid"
  where "currTidSystemState st = (currTid (scheduleState st))"

fun nextTidSystemState :: "'a System \<Rightarrow> 'a SystemState \<Rightarrow> Tid"
  where "nextTidSystemState sys st = currTid (scheduleNext (schedule sys) (scheduleState st))"

subsection \<open>Well-formed Scheduling States\<close>

text \<open>The collection of properties in this section formalizes the notion of 
a well-formed scheduling state.  A key property is a rather strong invariant
establishing a relationship between the current task that has executed and
the next to be executed.  This property is key to allowing the successor / predecessor
relation on task identifiers to be observed in a single schedule/system state.\<close>

text \<open>A strict version of the well-formedness property for Tids, stating that a
Tid in the currTid field must belong to the set of systemTids.  This property
DOES NOT hold in the initial state (because the currTid is the special Tid
identifier for the initialization state, but it does hold for every state
AFTER the initial state (and the result of every scheduleNext operation produces
a scheduling state that satisfies this property.\<close>

definition wf_ScheduleState_currTid_inSys :: "'store System \<Rightarrow> Tid \<Rightarrow> bool" where
  "wf_ScheduleState_currTid_inSys sys tid \<equiv> tid \<in> systemTids sys"

text \<open>The "looser" version of the property above that also allows the currTid
field to be the initTid.\<close>

definition wf_ScheduleState_currTid :: "'store System \<Rightarrow> Tid \<Rightarrow> bool" where
  "wf_ScheduleState_currTid sys tid \<equiv> (tid = initTid \<or>
                                        wf_ScheduleState_currTid_inSys sys tid)"

text \<open>The property below states that the nextSlotNum field is always a valid
(in range) index for the static schedule in the system (0-based indexing).\<close>

definition wf_ScheduleState_nextSlotNum :: "'store System \<Rightarrow> SlotNum \<Rightarrow> bool" where
  "wf_ScheduleState_nextSlotNum sys slotNum \<equiv> 
    0 \<le> slotNum \<and> slotNum < (length (schedule sys))"

text \<open>The main well-formedness property of the scheduleState is stated below.  The first two 
conjuncts simply enforce the well-formedness conditions on the currTid and nextSlotNum
fields as described above. Following that, we have a property that states the 
special condition that holds when we are in the initial scheduling state.  Finally, 
we have the most interesting property that enables us to establish a relationship between
the currTid and the Tid of the next task to be executed (enabling us to discern
the predecessor/successor relation on Tids).  Intuitively, the property states
the currentTid is what we looked up from the static schedule when we used the previous
slot number.  Proving well-formedness will rely on establishing that computePrevSlotNum
is an inverse of computeNextSlotNum.\<close>

definition wf_ScheduleState :: "'store System \<Rightarrow> ScheduleState \<Rightarrow> bool" where
  "wf_ScheduleState sys schst 
     \<equiv> wf_ScheduleState_currTid sys (currTid schst) \<and> 
       wf_ScheduleState_nextSlotNum sys (nextSlotNum schst) \<and>
       ((currTid schst) = initTid \<longrightarrow> (nextSlotNum schst) = initSlotNum) \<and> 
       ((currTid schst) \<noteq> initTid \<longrightarrow> 
           (currTid schst) = fetchTidFromSlot 
                                (schedule sys)
                                (computePrevSlotNum (schedule sys) (nextSlotNum schst)))"

text \<open>Define a simp set for the definitions above.\<close>

named_theorems wf_ScheduleState_simps
lemmas [wf_ScheduleState_simps] =
  wf_ScheduleState_currTid_def
  wf_ScheduleState_currTid_inSys_def
  wf_ScheduleState_nextSlotNum_def 
  wf_ScheduleState_def

section \<open>Helper Lemmas\<close>

subsection \<open>Helper Lemmas for System\<close>

lemma currTidInSysImpliesNotInitTid:
  assumes wf_model: "wf_Model m"
      and wf_sys: "wf_System sys m"
      and currTidInSys: "tid \<in> systemTids sys"
    shows "tid \<noteq> initTid"
  using currTidInSys wf_System_Tids_def wf_System_def wf_sys by auto

subsection \<open>Helper Lemmas for Schedule State\<close>

text \<open>The initial scheduling state is well-formed\<close>

lemma initSchedState_wf: 
  assumes wf_model: "wf_Model m"
      and wf_sys: "wf_System sys m"
  shows "wf_ScheduleState sys (initScheduleState (schedule sys))"
  using wf_sys by (simp add: wf_System_simps wf_ScheduleState_simps Suc_leI)

text \<open>The following lemma expresses (in terms of the scheduleState field-level well-formedness
properties) that the @{term computeNextSlotNum} function preserves well-formedness.\<close>

(* this field-level version of the computeNext wellformedness below may not be needed
if we typically have as an assumption that the schedule state is well-formed
in the current proof context.  That is, it may be more convenient for proofs
just to work with preconditions that the full scheduling state is well-formed. *)

lemma computeNextSlotNum_preserves_props:
  assumes wf_scheduleState: "wf_ScheduleState_nextSlotNum sys nxtSlotNum"
    shows "wf_ScheduleState_nextSlotNum 
              sys (computeNextSlotNum (schedule sys) nxtSlotNum)"
  using assms by (auto simp add: wf_ScheduleState_nextSlotNum_def)

text \<open>Now we have a variant of the property above that has a precondition
for well-formedness on the full scheduling state.\<close>

lemma computeNextSlotNum_preserves_wf:
  assumes  wf_scheduleState: "wf_ScheduleState sys schst"
    shows "wf_ScheduleState_nextSlotNum 
              sys (computeNextSlotNum (schedule sys) (nextSlotNum schst))"
 using assms by (auto simp add: wf_ScheduleState_simps)

text \<open>A similar property proves that the @{term computePreviousSlotNum}
function is well-formed.\<close>

(* ToDo: May want to refactor the names so that both the function and wf property
both use "Prev" *)

lemma computePreviousSlotNum_preserves_wf:
  assumes  wf_scheduleState: "wf_ScheduleState sys schst"
    shows "wf_ScheduleState_nextSlotNum 
              sys (computePrevSlotNum (schedule sys) (nextSlotNum schst))"
 using assms by (auto simp add: wf_ScheduleState_simps)

text \<open>Show that the fetch Tid operation establishes the strong version
of the currTid invariant (i.e., the currTid obtained always belongs
to the set of system Tids and is not the initTid).\<close>

lemma fetchTidFromSlot_preserves_wf:
  assumes wf_model: "wf_Model m"
      and wf_sys: "wf_System sys m"
      and  wf_scheduleState: "wf_ScheduleState sys schst"
    shows  "wf_ScheduleState_currTid_inSys 
                 sys (fetchTidFromSlot (schedule sys) (nextSlotNum schst))" 
  using assms
  by (simp add: wf_System_Schedule_def wf_System_def wf_ScheduleState_simps)
text \<open>Show computing previous slot is an inverse to computing the next slot.\<close>

lemma computePrev_computeNext_inverse:
  assumes wf_schedule: "wf_System_Schedule sys" 
      and wf_slotNum: "wf_ScheduleState_nextSlotNum sys slotNum"
    shows "slotNum = (computePrevSlotNum (schedule sys) (computeNextSlotNum (schedule sys) slotNum))"
using assms
  by (auto simp add: wf_System_simps wf_ScheduleState_simps)

text \<open>Finally, we prove that the scheduleNext operation preserves the well-formedness
property.  Moreover, the currTid field in the produced scheduling state actually
satisfies the stronger well-formedness property (it belongs to the system Tids).\<close>

lemma scheduleNext_preserves_wf:
  assumes wf_model: "wf_Model m"
      and wf_sys: "wf_System sys m"
      and wf_scheduleState: "wf_ScheduleState sys schst"
    shows "wf_ScheduleState sys (scheduleNext (schedule sys) schst)
          \<and> wf_ScheduleState_currTid_inSys sys (currTid(scheduleNext (schedule sys) schst))"
proof -
  \<comment> \<open>First, break down the well-formedness assumption on the input scheduleState to 
   finer grain properties on the fields.\<close>
  from wf_scheduleState have wf_currTid: 
     "wf_ScheduleState_currTid sys (currTid schst)" 
    by (auto simp only: wf_ScheduleState_def)
  from wf_scheduleState have wf_nextSlotNum: 
     "wf_ScheduleState_nextSlotNum sys (nextSlotNum schst)" 
    by (auto simp only: wf_ScheduleState_def)
  \<comment> \<open>Create names for import parts of the terms.\<close>
  let ?oldcurrTid = "currTid schst"
  let ?oldnextSlotNum = "nextSlotNum schst"
  let ?schedNext = "scheduleNext (schedule sys) schst"
  let ?newcurrTid = "currTid ?schedNext"
  let ?newnextSlotNum = "nextSlotNum ?schedNext"
  \<comment> \<open>Start by showing that the individual fields of the new scheduling state are well-formed,
      using previously established lemmas.\<close>
  \<comment> \<open>The new nextSlotNum is well-formed.\<close>
  from wf_sys wf_scheduleState have wf_newnextSlotNum: "wf_ScheduleState_nextSlotNum sys ?newnextSlotNum"
    using computeNextSlotNum_preserves_wf by force
  (* potential refactor the step below if I refactor the fetchTidFromSlot assumptions *)
   \<comment> \<open>The new currTid satisfies the strong well-formedness property (belongs to systemTids).\<close>
  from wf_sys wf_scheduleState have wf_newcurrTid_inSys: "wf_ScheduleState_currTid_inSys sys ?newcurrTid" 
    using wf_nextSlotNum fetchTidFromSlot_preserves_wf wf_model by auto
   \<comment> \<open>From this we know that it satisfies the weaker well-formedness property.\<close>
  from wf_newcurrTid_inSys have wf_newcurrTid: "wf_ScheduleState_currTid sys ?newcurrTid"
    unfolding wf_ScheduleState_currTid_def by auto
   \<comment> \<open>Now to establish the complex relationship in the new scheduling state between
      currTid and slotNum...
      First, establish the condition necessary to select the slot number property 
      (init situation vs non-init situation) to enforce.
      Specifically, show that the new state is not the initial scheduling state.\<close>
  from wf_sys \<comment> \<open>from this, we know that the @{term initTid} is not in the system Tids\<close>
       wf_newcurrTid_inSys \<comment> \<open>From this, we know that the newcurrTid IS in the system Tids\<close>
    \<comment> \<open>Therefore, we can conclude that it is not the @{term initTid}.\<close>
    have newcurrTid_not_initTid: "?newcurrTid \<noteq> initTid"
    unfolding wf_ScheduleState_currTid_inSys_def by (auto simp add: wf_System_simps)
  \<comment> \<open>Show that the complex relationship between the new currTid and slot status is correct
      (i.e., the currTid must have come from the previous slot.\<close>
  \<comment> \<open>First, we form the term used to compute the new currTid from the previous state's
      nextSlotNum (i.e., ?oldnextSlotNum).\<close>
  have "?newcurrTid = fetchTidFromSlot (schedule sys) ?oldnextSlotNum" by simp
  \<comment> \<open>Now we need to relate the oldnextSlotNum to the newnextSlotNum via the 
      computePrevious function.
     First, we instantiate the inverse property previously proved.\<close>
  from wf_sys wf_scheduleState have
   h1: "?oldnextSlotNum = (computePrevSlotNum (schedule sys) 
                                          (computeNextSlotNum (schedule sys) ?oldnextSlotNum))"
    using computePrev_computeNext_inverse by (auto simp add: wf_System_simps wf_ScheduleState_simps)
  \<comment> \<open>Now we recognize that the newnextSlotNum was computed from the old one using the 
     same pattern that appears as a subterm above.\<close>
  have 
   h2: "?newnextSlotNum = (computeNextSlotNum (schedule sys) ?oldnextSlotNum)" by simp
  \<comment> \<open>Now we can form the term that appears in the well-formedness conditions for the 
  new scheduling state capturing the complex relationship between the currTid and previous 
  slot number.\<close>
  from h1 h2 have h3: 
   "?newcurrTid = fetchTidFromSlot 
                    (schedule sys) 
                    (computePrevSlotNum (schedule sys) ?newnextSlotNum)" by simp
  \<comment> \<open>And then the thesis is proved from the various bits above.\<close>
  from wf_newcurrTid wf_newcurrTid_inSys wf_newnextSlotNum newcurrTid_not_initTid h3 show ?thesis
    unfolding wf_ScheduleState_def by blast
qed

text \<open>Well-Formedness for SystemStates\<close>

definition wf_SystemState_systemTasks_dom :: "Model \<Rightarrow> 'a SystemState \<Rightarrow> bool"
  where "wf_SystemState_systemTasks_dom m ss \<equiv>
          (modelTids m) = dom (systemTasks ss)"

definition wf_SystemState_systemTasks :: "Model \<Rightarrow> 'a SystemState \<Rightarrow> bool"
  where "wf_SystemState_systemTasks m ss \<equiv>
            \<forall>tid \<in> dom (systemTasks ss) . 
                wf_TaskState ((modelTaskDescrs m) $ tid) ((systemTasks ss) $ tid)"

definition wf_SystemState :: "Model \<Rightarrow> 'a System \<Rightarrow> 'a SystemState \<Rightarrow> bool"
  where "wf_SystemState m sys ss \<equiv> 
          wf_SystemState_systemTasks_dom m ss
        \<and> wf_SystemState_systemTasks m ss
        \<and> wf_ChState (modelChIds m) (systemChs ss)
        \<and> wf_ScheduleState sys (scheduleState ss)"

named_theorems wf_SystemState_simps
lemmas [wf_SystemState_simps] =
  wf_SystemState_systemTasks_dom_def
  wf_SystemState_systemTasks_def
  wf_SystemState_def

end
