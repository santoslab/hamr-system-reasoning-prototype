theory HAMRMicro05Model 
  imports Main SetsAndMaps "HOL-Library.FSet" HOL.Finite_Set
begin

section \<open>Model Representation (Static Structurae)\<close>

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

text \<open>For the purposes of abstracting the schedule away from the task we introduce a
      set of Ready Ids that are the set of resources available to be used for the perti
      net representation of the schedule. The ready ids represent places in the petri net
      and are used to show where tokens are in the petri net.

      An RID can be referred to as a place\<close>

type_synonym Rid = nat
type_synonym Rids = "Rid fset"

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
A system (model) description includes its channel identifiers, all place identifiers,
a table associating its task identifiers to task descriptors, the set of RIDs (set of places),
and the START and END RIDs. We have decided to use "Model" as the name of this structure
since that corresponds to the HAMR "Model" definition in
Model.thy\<close>

record Model =
  modelTaskDescrs :: "(Tid, TaskDescr) map"  
  modelChIds :: "ChIds"
  modelReadyIds :: "Rids"
  modelStartRid :: "Rid"
  modelEndRid :: "Rid"

text \<open>Helper function to return the component identifiers in model m (similar to modelCIDs 
in HAMR Model.thy).\<close>

fun modelTids:: "Model \<Rightarrow> Tids"
  where "modelTids m = dom (modelTaskDescrs m)"

text \<open>Used to ensure that the Ready Ids of the model must be greater than or equal to the number of
      tids in the model as the least complicated petri net would be a strict total ordering which, 
      in the smallest case, would be simply one input place for each transition\<close>

definition wf_Model_Rids :: "Model \<Rightarrow> bool"
  where "wf_Model_Rids m \<equiv> card (modelTids m) \<le> fcard (modelReadyIds m)
                            \<and> modelStartRid m |\<in>| (modelReadyIds m)
                            \<and> modelEndRid m |\<in>| (modelReadyIds m)
                            \<and> modelStartRid m \<noteq> modelEndRid m"


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
  where "wf_Model m \<equiv> wf_Model_TaskDescrs m \<and> wf_Model_Tids m \<and> wf_Model_InHasUniqueOut m \<and> wf_Model_Rids m"
                      

named_theorems wf_Model_simps
lemmas [wf_Model_simps] =
  wf_Model_TaskDescrs_def
  wf_Model_Tids_def
  wf_Model_InHasUniqueOut_def
  wf_Model_Rids_def
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

subsection \<open>Abstract Schedule\<close>

text \<open>Maps a set of the ready ids to another set of ready ids. This map will act as the
      transition structure of a Petri net. An element of the domain represents the set of places
      that need to have a token in them to fire the transition, and the corresponding element of 
      the codomain represents what places will have have token in them as a result of firing the transition.

      For the purposes of documentation, a transition will be referred to by the places required to fire
      the transition. When specifically talking about the required places we will say the set of 
      in/input places or input and the places that result from firing the transition will be referred 
      to as the out/output places or output

      The domain of next rel is the set of  all transitions in the system\<close>

type_synonym Next = "(Rid fset, Rid fset) map"

subsection \<open>Schedule State (Dynamic/runtime data structure)\<close>

text \<open>Represents what places in the Petri net have a token in them and is used to calculate which
      transitions are available at a given point in the execution of the system. This is used
      in the system state to represent the schedule state. 

      This set can be referred to as the schedule state of st or (ready st) and can be specifically
      represent by {|p1, p2, ..., pn|}

      A transition is considered fireable if the set on in places is a subset of READY\<close>
type_synonym Ready = "Rid fset"

text \<open>Calculates the next ready set given a transition (defined by its input places) by removing 
      all ready IDs tied to the input places from the set and adding the ready IDs tied to the 
      output places of the transition.\<close>
fun scheduleNextBody :: "Next \<Rightarrow> Ready \<Rightarrow> Rid fset \<Rightarrow> Ready"
  where "scheduleNextBody n r rf = r - (rf :: nat fset) |\<union>| n $ rf"

text \<open>This is an extension of scheduleNextBody used to enable cyclic scheduling in a controlled
      manner by separating the execution of a single pass of the schedule from the cycle. This is
      done by making {|END|} a possible choice in the execution semantics and, when it is chosen, 
      it resets the schedule state back to {|START|}. The is a sound extension of the scheduleNext
      function as {|END|} can only be a choice if the schedule state is {|END|} by the proper
      completion WF condition.

       Schedule state will always be {|END|} 
            when this update happens
                     |
                     V
      {|START|} = {|END|} - {|END|} \<union> {|START|} (Exact same structure as scheduleNextBody)

      The same well-formedness condition can be used as the body has the same restrictions as the
      acyclic version of the system and the cycle is well-defined.\<close>
(* NEW NEXT FUNCTION THAT WILL BE USED BY THE EXECUTION SEMANTICS*)
fun scheduleNextTotal :: "Next \<Rightarrow> Model \<Rightarrow> Ready \<Rightarrow> Rid fset \<Rightarrow> Ready"
  where "scheduleNextTotal next m r rf = (if (rf = {|modelEndRid m|})
                                          then {|modelStartRid m|}
                                          else scheduleNextBody next r rf)"

text \<open>The system is able to step from schedule state r1 to another schedule state r2 if there exist 
      an transition t whose input places are a subset of r1 and is in the domain of the next relation 
      such that the r2 is the result of progressing the scheduled with r1 and transition t\<close>

definition scheduleStepBody :: "Next \<Rightarrow> Ready \<Rightarrow> Ready \<Rightarrow> bool"
  where "scheduleStepBody next r1 r2 \<equiv> \<exists> t. t \<in> {s. s |\<subseteq>| r1 \<and> s \<in> (dom next)}
                                        \<and> (scheduleNextBody next r1 t = r2)"

definition scheduleReachBody :: "Next \<Rightarrow> Ready \<Rightarrow> Ready \<Rightarrow> bool" where 
 "scheduleReachBody next init r = ((scheduleStepBody next)\<^sup>*\<^sup>* init r)"


definition scheduleReachBodySet :: "Next \<Rightarrow> Ready \<Rightarrow> Rid set"
  where "scheduleReachBodySet next readySet \<equiv> {r. \<exists>rset. scheduleReachBody next readySet rset \<and> r |\<in>| rset}"

text \<open>Well Formedness Properties for schedule state is stated lower in the file\<close>

subsection \<open>System State\<close>

text \<open>A system state consists of the channel state and task state for each task in the system, 
the previous tasks and channel state, and the schedule state. This is a simplification of HAMR's 
system state (see HAMR SystemState.thy) that includes a states for each thread and the state of the 
communication substrate.\<close>

record 'a SystemState =
  systemTasks :: "(Tid, 'a TaskState) map" \<comment> \<open>states of each task\<close>
  systemChs :: "'a ChState" \<comment> \<open>state of communication substrate\<close>
  ready :: Ready \<comment> \<open>available scheduling resources\<close>
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

subsection \<open>System Specification\<close>

text \<open>Maps task IDs to their corresponding task.\<close>
type_synonym 'value TaskMap = "(Tid, 'value Task) map"

text \<open>Maps sets of ready IDs to task ids. This is used to represent which transition 
      correspond to a certain task/component. Any transition (defined by its input places) 
      in the domain of the map is considered a component transition and any transition not in the 
      domain of the map is considered a control point transition\<close>

type_synonym RidToTidMap = "(Rid fset, Tid) map"

text \<open>A system specification includes an initial state, a data structure holding
all the task specifications, a Petri net that represents all schedule constraints for the system,
and a data structure holding what transitions in the Petri net are tied to components/tasks\<close>

record 'value System =
  initSystemState :: "'value SystemState"
  taskMap :: "'value TaskMap"
  nextRel :: Next
  activationMap :: RidToTidMap

subsubsection \<open>Action Map WF Condtions\<close>

text \<open>For an activation map to be wellformed
        . All sets of ready IDs in the domain of the activation map must be a subset of all readyIDs
          of the model and must be in the domain of the next relation
        . All tasks IDs in the range must also be in the taskMap's domain\<close>

definition wf_System_ActivationMap :: "'value System \<Rightarrow> Model \<Rightarrow> bool"
  where "wf_System_ActivationMap sys m \<equiv> 
      (\<forall>rids \<in> dom (activationMap sys). rids |\<subseteq>| (modelReadyIds m) \<and> rids \<in> dom (nextRel sys))
      \<and> ran (activationMap sys) \<subseteq> dom (taskMap sys)"


subsubsection \<open>Next Relation WF Condtions\<close>

text \<open>All distinct transitions must have disjoint sets of in places which enforces that once a 
      choice is made to fire there is only one transition that can fire. Enforces that petri net 
      is a free-choice net. 

      This will also be used to enforce no loops since all reachable marking must be able to reach
      the output and since no choice is allowed you cannot choose to leave a loop.\<close>
definition wf_System_NextRel_DisjointDom :: "'value System \<Rightarrow> bool"
  where "wf_System_NextRel_DisjointDom sys \<equiv>
          \<forall>d1 \<in> dom (nextRel sys).
            \<forall> d2 \<in> dom (nextRel sys). (d1 \<noteq> d2 \<longrightarrow> fset d1 \<inter> fset d2 = {})"

text \<open>The union of the domain should cover all RIDs but the END rid\<close>
definition wf_System_NextRel_DomUnion :: "'value System \<Rightarrow> Model \<Rightarrow> bool"
  where "wf_System_NextRel_DomUnion sys m \<equiv>
          \<Union> (fset`(dom (nextRel sys))) = fset((modelReadyIds m) |-| {|modelEndRid m|})"

text \<open>The union of the codomain should cover all RIDS but the START rid\<close>
definition wf_System_NextRel_RanUnion :: "'value System \<Rightarrow> Model \<Rightarrow> bool"
  where "wf_System_NextRel_RanUnion sys m \<equiv>
          \<Union> (fset`the`(nextRel sys)`(dom (nextRel sys))) = fset((modelReadyIds m) |-| {|modelStartRid m|})"

text \<open>No two distinct transitions can have the same set of out places. This enforce that you cannot 
      have loops connected to the start since a reachable loop must have a place that is initially 
      entered to and returned to upon loop completion.

      This along with wf_System_NextRel_DisjointDom and wf_System_NextRel_PlaceOnPath implies
      the loop cannot exist since it can neither be entered or exited which mean the loop cannot
      be connected to rest of the net which violates wf_System_NextRel_PlaceOnPath.\<close>
definition wf_System_NextRel_DisjointRan :: "'value System \<Rightarrow> bool"
  where "wf_System_NextRel_DisjointRan sys \<equiv>
          \<forall>d1 \<in> dom (nextRel sys).
            \<forall> d2 \<in> dom (nextRel sys). (d1 \<noteq> d2 \<longrightarrow> (nextRel sys $ d1) |\<inter>| (nextRel sys $ d2) = {||})"

text \<open>START and END must be a source and sink of the Next Relation respectively, START cannot
      appear in the out places of any transition, and END cannot appear in any of the in places
      of any transition

      Required for WF-net\<close>
definition wf_System_NextRel_SourceAndSink :: "'value System \<Rightarrow> Model \<Rightarrow> bool"
  where "wf_System_NextRel_SourceAndSink sys m \<equiv>
           \<not>(\<exists>x \<in> ran(nextRel sys). modelStartRid m |\<in>| x)
           \<and> \<not>(\<exists>x \<in> dom(nextRel sys). modelEndRid m |\<in>| x)
           \<and> {|modelStartRid m|} \<in> dom(nextRel sys)
           \<and> {|modelEndRid m|} \<in> ran(nextRel sys)"

text \<open>For all transitions, the transition is a task/component transition if and only if there is 
      one input and one output

      Defines a component/task/sequent transition\<close>
definition wf_NextRel_TaskTransinition :: "'value System \<Rightarrow> Model \<Rightarrow> bool"
  where "wf_NextRel_TaskTransinition sys m \<equiv>
          \<forall>c \<in> dom (nextRel sys).
            c \<in> dom (activationMap sys)
            \<longleftrightarrow>
            fcard c = 1 \<and> fcard (nextRel sys $ c) = 1"

text \<open>For all transitions, if there is more than one output place, then there is only one input place
      and it is a control point transition

      Defines a Split transition\<close>
definition wf_NextRel_Split :: "'value System \<Rightarrow> Model \<Rightarrow> bool"
  where "wf_NextRel_Split sys m \<equiv>
          \<forall>c \<in> dom (nextRel sys).
            fcard (nextRel sys $ c) > 1
            \<longrightarrow> 
            fcard c = 1 \<and> c \<notin> dom (activationMap sys)"

text \<open>For all transition, if there is more than one input place, then there is only one output place
      and it is a control point transition
    
      Defines a Join transition\<close>
definition wf_NextRel_Join :: "'value System \<Rightarrow> Model \<Rightarrow> bool"
  where "wf_NextRel_Join sys m \<equiv>
          \<forall>c \<in> dom (nextRel sys).
            fcard c > 1
            \<longrightarrow> 
            fcard (nextRel sys $ c) = 1 \<and> c \<notin> dom (activationMap sys)"

text \<open>If a transition is a split, then all output places must be the input to a split or task transition\<close>
definition wf_NextRel_SplitNext :: "'value System \<Rightarrow> Model \<Rightarrow> bool"
  where "wf_NextRel_SplitNext sys m \<equiv> 
          \<forall>c \<in> dom (nextRel sys).
            fcard (nextRel sys $ c) > 1
            \<longrightarrow>
            (\<forall>p |\<in>| (nextRel sys $ c). {|p|} \<in> dom(nextRel sys))"

text \<open>If a transition is a join, then all input places must be the result of a task or join transition\<close>
definition wf_NextRel_JoinPrev :: "'value System \<Rightarrow> Model \<Rightarrow> bool"
  where "wf_NextRel_JoinPrev sys m \<equiv>
          \<forall>c \<in> dom (nextRel sys).
            fcard c > 1
            \<longrightarrow>
            (\<forall>p |\<in>| c. 
              \<exists>c' \<in> dom (nextRel sys).
                (nextRel sys $ c') = {|p|}
                \<and>
                (
                  c' \<in> dom (activationMap sys)
                  \<or>
                  fcard c' > 1
                )
            )"

text \<open>All transitions are splits, joins, or sequents\<close>
definition wf_NextRel_AllPossibleTransitions :: "'value System \<Rightarrow> Model \<Rightarrow> bool"
  where "wf_NextRel_AllPossibleTransitions sys m \<equiv>
          \<forall>c \<in> dom (nextRel sys).
            (fcard c = 1 \<and> fcard (nextRel sys $ c) = 1)
            \<or> (fcard c = 1 \<and> fcard (nextRel sys $ c) > 1)
            \<or> (fcard c > 1 \<and> fcard (nextRel sys $ c) = 1)"

text \<open>The set of in places and out places for a transition must be disjoint\<close>
definition wf_NextRel_NoReinsert :: "'value System \<Rightarrow> Model \<Rightarrow> bool"
  where "wf_NextRel_NoReinsert sys m \<equiv> \<forall>c \<in> dom (nextRel sys). c |\<inter>| (nextRel sys $ c) = {||}"
       
text \<open>All places must be on a path from {|START|} to {|END|}. To enforce this within this framework, 
      we say that a place must appear in a marking M from {|START|} and a step must be made that unmarks 
      the place in M' in such a way that M' can reach the {|END|}.

      Required to be a WF-net.\<close>
definition wf_System_NextRel_PlaceOnPath :: "'value System \<Rightarrow> Model \<Rightarrow> bool"
  where "wf_System_NextRel_PlaceOnPath sys m \<equiv>
          \<forall>rid \<in> fset (modelReadyIds m). 
            \<exists>M M'. scheduleReachBody (nextRel sys) {|modelStartRid m|} M 
                \<and> rid |\<in>| M
                \<and> rid |\<notin>| M'
                \<and> scheduleStepBody (nextRel sys) M M'
                \<and> scheduleReachBody (nextRel sys) M' {|modelEndRid m|}"

text \<open>All transitions must be on a path from {|START|} to {|END|}. To enforce this within this 
      framework, we say that a transition must be enabled in a marking M from {|START|} and a step 
      must be made that disables the transition in M' (fires the transition) in such a way that M' 
      can reach the {|END|}.

      Required to be a WF-net.\<close>
definition wf_System_NextRel_TransitionOnPath :: "'value System \<Rightarrow> Model \<Rightarrow> bool"
  where "wf_System_NextRel_TransitionOnPath sys m \<equiv>
          \<forall>rids \<in> dom (nextRel sys). 
            \<exists>M M'. scheduleReachBody (nextRel sys) {|modelStartRid m|} M 
                \<and> rids |\<subseteq>| M
                \<and> \<not>(rids |\<subseteq>| M')
                \<and> scheduleStepBody (nextRel sys) M M'
                \<and> scheduleReachBody (nextRel sys) M' {|modelEndRid m|}"

text \<open>From {|START|}, if a state is reachable then the state must be able to reach the {|END|}

      Required for WF-net soundness\<close>
definition wf_System_NextRel_OptToComplete :: "'value System \<Rightarrow> Model \<Rightarrow> bool"
  where "wf_System_NextRel_OptToComplete sys m \<equiv> 
          \<forall>mark. scheduleReachBody (nextRel sys) {|modelStartRid m|} mark 
                 \<longrightarrow> scheduleReachBody (nextRel sys) mark {|modelEndRid m|}"

text \<open>If a state is reachable from {|START|} and it contains END then the state is {|END|}.

      Required for WF-net soundness\<close>
definition wf_System_NextRel_ProperComplete :: "'value System \<Rightarrow> Model \<Rightarrow> bool"
  where "wf_System_NextRel_ProperComplete sys m \<equiv>  
          \<forall>mark. (scheduleReachBody (nextRel sys) {|modelStartRid m|} mark \<and> modelEndRid m |\<in>| mark)
            \<longrightarrow> mark = {|modelEndRid m|}"

text \<open>For all transitions t, there must exist a marking reachable from {|START|} where t is enabled.

      Required for WF-net soundness\<close>
definition wf_System_NextRel_NoDeadTransitions :: "'value System \<Rightarrow> Model \<Rightarrow> bool"
  where "wf_System_NextRel_NoDeadTransitions sys m \<equiv> 
          \<forall>t \<in> (dom (nextRel sys)). 
            \<exists>M. scheduleReachBody (nextRel sys) {|modelStartRid m|} M \<and> t |\<subseteq>| M"

text \<open>For reachable schedule states, the state cannot the in places and the out places of a transition.

      Required for AFC-WF-Net\<close>
definition wf_System_NoCycle :: "'value System \<Rightarrow> Model \<Rightarrow> bool"
  where "wf_System_NoCycle sys m \<equiv>
          \<forall>schst. scheduleReachBody (nextRel sys) {|modelStartRid m|} schst
                  \<longrightarrow>
                  (\<forall>t \<in> (dom (nextRel sys)). \<not>(t |\<subseteq>| schst \<and> (nextRel sys $ t) |\<subseteq>| schst))"

text \<open>We make the assumption that the provided Petri net is a sound workflow net due to properties
      described in "Soundness of workflow nets: classification, decidability, and analysis (Aalst)".
      These properties will either be proven correct for the grammar or can be checked in the final
      tool\<close>

definition nextRel_Assumptions :: "'value System \<Rightarrow> Model \<Rightarrow> bool"
  where "nextRel_Assumptions sys m \<equiv>
          wf_System_NextRel_PlaceOnPath sys m
          \<and> wf_System_NextRel_TransitionOnPath sys m
          \<and> wf_System_NextRel_OptToComplete sys m
          \<and> wf_System_NextRel_ProperComplete sys m
          \<and> wf_System_NextRel_NoDeadTransitions sys m
          \<and> wf_System_NoCycle sys m "

text \<open>Along with the above properties the Petri net 
        1) must have least one transition
        2) all sets of in places and out places must be a subset of all RIDs
        3) the domain is finite
        4) the range is finite
        5) the empty set should not be in the domain
        6) the empty set should not be in the range\<close>

definition wf_System_NextRel :: "'value System \<Rightarrow> Model \<Rightarrow> bool"
  where "wf_System_NextRel sys m \<equiv> card (dom (nextRel sys)) > 0
                                 \<and> (\<forall>rids \<in> (dom (nextRel sys) \<union> ran (nextRel sys)). rids |\<subseteq>| (modelReadyIds m))
                                 \<and> finite (dom (nextRel sys))
                                 \<and> finite (ran (nextRel sys))
                                 \<and> {||} \<notin> (dom (nextRel sys))
                                 \<and> {||} \<notin> (ran (nextRel sys))
                                 \<and> wf_System_NextRel_DisjointDom sys
                                 \<and> wf_System_NextRel_DisjointRan sys
                                 \<and> wf_System_NextRel_DomUnion sys m
                                 \<and> wf_System_NextRel_RanUnion sys m
                                 \<and> wf_System_NextRel_SourceAndSink sys m
                                 \<and> wf_NextRel_TaskTransinition sys m
                                 \<and> wf_NextRel_Split sys m
                                 \<and> wf_NextRel_Join sys m
                                 \<and> wf_NextRel_SplitNext sys m
                                 \<and> wf_NextRel_JoinPrev sys m
                                 \<and> wf_NextRel_AllPossibleTransitions sys m
                                 \<and> wf_NextRel_NoReinsert sys m"

subsubsection \<open>Task Map WF\<close>
text \<open>For all task maps
        . the Tids in the domain must be Tids that belong to the model and vice versa
        . all task IDs in the domain of the task map must correspond to the task ID of the 
          corresponding task in the map\<close>

definition wf_System_TaskMap :: "'value System \<Rightarrow> Model \<Rightarrow> bool"
  where "wf_System_TaskMap sys m \<equiv> (modelTids m) = dom (taskMap sys)
                                  \<and> (\<forall>tid \<in> dom (taskMap sys). taskId ((taskMap sys) $ tid) = tid)"

subsubsection \<open>Task Action WF Conditions\<close>

text \<open>The value of all out ports only depends on the in ports or does not depend on any port\<close>
definition wf_System_ChState_In :: "'value System \<Rightarrow> Model \<Rightarrow> bool"
  where "wf_System_ChState_In sys m \<equiv>
          \<comment> \<open>for all task\<close>
          \<forall>tid \<in> (dom (taskMap sys)). 
              \<comment> \<open>for any two states\<close>
              \<forall>(st1 :: 'value SystemState) (st2 :: 'value SystemState).
                \<comment> \<open>if for all in-channels, st1 and st2 are equal\<close>
                (\<forall>c \<in> (inChIds ((modelTaskDescrs m) $ tid)). (systemChs st1) $ c = (systemChs st2) $ c) 
                \<comment> \<open>then for all out channels, st1' and st2' are equal\<close>
                \<longrightarrow> (\<forall>c' \<in> (outChIds ((modelTaskDescrs m) $ tid)).
                        \<comment> \<open>the update to the channel is the same\<close>
                        ((snd ((action ((taskMap sys) $ tid)) ((systemTasks st1) $ tid, systemChs st1))) $ c' 
                         = (snd ((action ((taskMap sys) $ tid)) ((systemTasks st2) $ tid, systemChs st2))) $ c') \<or>
                        \<comment> \<open>or the action does not affect the out-port\<close>
                        ((systemChs st1) $ c' = (snd ((action ((taskMap sys)  $ tid)) ((systemTasks st1) $ tid, systemChs st1))) $ c' \<and>
                         (systemChs st2) $ c' = (snd ((action ((taskMap sys)  $ tid)) ((systemTasks st2) $ tid, systemChs st2))) $ c'))"

text \<open>If a channel is not an out channel for a task then the value should not be modified by the action\<close>
definition wf_System_ChState_Out :: "'value System \<Rightarrow> Model \<Rightarrow> bool"
  where "wf_System_ChState_Out sys m \<equiv> 
            \<comment> \<open>for all tasks\<close>
            \<forall>tid \<in> (dom (taskMap sys)).
              \<comment> \<open>for all states\<close>
              \<forall>(st :: 'value SystemState).
                \<comment> \<open>if a channel is not an out channel\<close>
                \<forall>c. c \<notin> (outChIds ((modelTaskDescrs m) $ tid)) \<longrightarrow>  
                  \<comment> \<open>then the value of the channel in the pre-state should equal the value of the channel in the post-state\<close>
                  (systemChs st) $ c = (snd ((action ((taskMap sys)  $ tid)) ((systemTasks st) $ tid, systemChs st))) $ c"

text \<open>System actions preserve the well-formedness of the channel state\<close>
definition wf_System_ActionsChState :: "'value System \<Rightarrow> Model \<Rightarrow> bool"
  where "wf_System_ActionsChState sys m \<equiv>
          \<comment> \<open>For all ready id sets in the system..\<close>
          \<forall>rf \<in> (dom (taskMap sys)). 
           \<comment> \<open>For all possible action inputs\<close>
           \<forall>(tscs :: ('value TaskState \<times> 'value ChState)). 
           \<comment> \<open>If the channel state is well-formed wrt the model-declared channel ids..\<close>
            wf_ChState (modelChIds m) (snd tscs) \<longrightarrow> 
           \<comment> \<open>..then the channel state produced by the action is well-formed wrt the model-declared channel ids.\<close>
            wf_ChState (modelChIds m) (snd ((action ((taskMap sys) $ rf)) tscs))"

text \<open>System actions preserve the well-formedness of task states, i.e., 
    for all task actions,
     for all task inputs (ts, cs)
      if the input task state ts is well-formed wrt the model,
       then the output task state that results from running the action is well-formed.\<close>

definition wf_System_ActionsTaskState :: "'value System \<Rightarrow> Model \<Rightarrow> bool"
  where "wf_System_ActionsTaskState sys m \<equiv>
          \<comment> \<open>For all task ids in the system..\<close>
          \<forall>rf \<in> (dom (taskMap sys)). 
           \<comment> \<open>For all possible action inputs\<close>
           \<forall>(tscs :: ('value TaskState \<times> 'value ChState)). 
             \<comment> \<open>If the task state ts is well-formed wrt the model-declared task descriptor...\<close>
             wf_TaskState ((modelTaskDescrs m) $ (taskId ((taskMap sys) $ rf))) (fst tscs) \<longrightarrow>  
             \<comment> \<open>..then the task state produced by the action is well-formed 
                 wrt the model-declared task descriptor.\<close>
             wf_TaskState ((modelTaskDescrs m) $ (taskId ((taskMap sys) $ rf))) 
                          (fst ((action ((taskMap sys) $ rf)) tscs))"

subsubsection \<open>Initial State WF Conditions\<close>

text \<open>The initial schedule state should just be START\<close>
definition wf_System_init :: "'value System \<Rightarrow> Model \<Rightarrow> bool" 
  where "wf_System_init sys m \<equiv> (ready (initSystemState sys)) = {|modelStartRid m|}"

definition wf_System :: "'value System \<Rightarrow> Model \<Rightarrow> bool" 
  where "wf_System sys m \<equiv> wf_System_ActivationMap sys m \<and>
                           wf_System_NextRel sys m \<and> 
                           wf_System_ActionsChState sys m \<and>
                           wf_System_ActionsTaskState sys m \<and>
                           wf_System_TaskMap sys m \<and>
                           wf_System_ChState_In sys m \<and>
                           wf_System_ChState_Out sys m \<and>
                           wf_System_init sys m"

named_theorems wf_System_simps
lemmas [wf_System_simps] =
  wf_System_ActivationMap_def
  wf_System_NextRel_def
  wf_System_def
  wf_System_ActionsChState_def
  wf_System_ActionsTaskState_def
  wf_System_TaskMap_def
  wf_System_ChState_In_def
  wf_System_ChState_Out_def
  wf_System_NextRel_DisjointDom_def
  wf_System_NextRel_DisjointRan_def
  wf_System_NextRel_DomUnion_def
  wf_System_NextRel_RanUnion_def
  wf_System_NextRel_TransitionOnPath_def
  wf_System_NextRel_OptToComplete_def
  wf_System_NextRel_ProperComplete_def
  wf_System_NextRel_NoDeadTransitions_def
  wf_System_NoCycle_def
  wf_NextRel_TaskTransinition_def
  wf_NextRel_Split_def
  wf_NextRel_Join_def
  wf_NextRel_SplitNext_def
  wf_NextRel_JoinPrev_def
  wf_NextRel_AllPossibleTransitions_def
  wf_NextRel_NoReinsert_def
  wf_System_init_def

subsection \<open>Is Run Net\<close>

text \<open>In order to make some assumption about reversability of steps it needs to be proven
      that the petri net is a run net meaning that each place has only one in transition and one 
      out transition\<close>

text \<open>Only one transition should have a place p as an in place

      {d \<in> dom (nextRel sys). p |\<in>| d} is the set of all transitions with p as an in place\<close>
lemma runNet_In: "wf_System sys m 
                  \<longrightarrow> (\<forall>p |\<in>| modelReadyIds m - {|modelStartRid m, modelEndRid m|}. 
                        card {d. d \<in> dom(nextRel sys) \<and> p |\<in>| d} = 1)"
  apply clarify
  apply (rule ccontr)
proof -
  fix p
  assume wf_sys: "wf_System sys m"
  assume isRid: "p |\<in>| modelReadyIds m"
  assume notStart: "p \<noteq> modelStartRid m"
  assume notEnd: "p \<noteq> modelEndRid m"
  assume notEmpty: " p |\<notin>| {||}"
  assume not1: "card {d \<in> dom (nextRel sys). p |\<in>| d} \<noteq> 1"

  \<comment> \<open>the cardinality of the set is 0 or greater than 1\<close>
  from not1 have "card {d \<in> dom (nextRel sys). p |\<in>| d} = 0 \<or> card {d \<in> dom (nextRel sys). p |\<in>| d} > 1"
    by auto

  then show False
  proof
    assume emptySet: "card {d \<in> dom (nextRel sys). p |\<in>| d} = 0"

    \<comment> \<open>There should exist a transition with p as an in place due to the covering requirement
        of the domain and the model RIDs\<close>
    from isRid wf_sys notEnd have "\<exists>d \<in> dom(nextRel sys). p |\<in>| d"
      apply (simp add: wf_System_def wf_System_NextRel_def wf_System_NextRel_DomUnion_def)
      by blast

    \<comment> \<open>There should exist an element in the following set\<close>
    from this have existX: "\<exists>x. x \<in> {d \<in> dom (nextRel sys). p |\<in>| d}"
      by auto

    \<comment> \<open>The set should be finite since the domain is finite\<close>
    from wf_sys have "finite {d \<in> dom (nextRel sys). p |\<in>| d}"
      by (simp add: wf_System_def wf_System_NextRel_def)

    \<comment> \<open>The cardinality of the set should be greater than 0\<close>
    from this existX have "card {d \<in> dom (nextRel sys). p |\<in>| d} > 0"
      using emptySet by auto

    \<comment> \<open>Contradiction\<close>
    from this emptySet show False
      by simp 
  next
    assume bigSet: "card {d \<in> dom (nextRel sys). p |\<in>| d} > 1"

    \<comment> \<open>The set should be finite\<close>
    from wf_sys have finiteSet: "finite {d \<in> dom (nextRel sys). p |\<in>| d}"
      by (simp add: wf_System_def wf_System_NextRel_def)

    \<comment> \<open>There should exist at least two distinct elements in the set\<close>
    from finiteSet bigSet have "\<exists>d1 d2. d1 \<noteq> d2 
                                        \<and> d1 \<in> {d \<in> dom (nextRel sys). p |\<in>| d}
                                        \<and> d2 \<in> {d \<in> dom (nextRel sys). p |\<in>| d}"
      by (metis (lifting) card.empty is_singletonI' is_singleton_altdef not_one_le_zero order.asym verit_comp_simplify1(3))

    then obtain d1 d2 where d1d2Def: "d1 \<noteq> d2 
                              \<and> d1 \<in> {d \<in> dom (nextRel sys). p |\<in>| d}
                              \<and> d2 \<in> {d \<in> dom (nextRel sys). p |\<in>| d}"
      by auto

    \<comment> \<open>p should be in d1 and d1 should be an element of the domain\<close>
    from d1d2Def have d1Def: "p |\<in>| d1 \<and> d1 \<in> dom(nextRel sys)"
      by simp
    \<comment> \<open>p should be in d2 and d2 should be an element of the domain\<close>
    from d1d2Def have d2Def: "p |\<in>| d2 \<and> d2 \<in> dom(nextRel sys)"
      by simp

    \<comment> \<open>Contradiction since domains should be disjoint if they are not equal\<close>
    from d1Def d2Def d1d2Def wf_sys show False
      by (auto simp add: wf_System_def wf_System_NextRel_def wf_System_NextRel_DisjointDom_def)
  qed
qed

text \<open>Only one transition should have a place p as an out place

      {d \<in> dom (nextRel sys). p |\<in>| the (nextRel sys d)} is the set of all transitions with p
      as an out place\<close>
lemma runNet_Out': "\<And>p. wf_System sys m 
                       \<Longrightarrow> card {d \<in> dom (nextRel sys). p |\<in>| the (nextRel sys d)} \<noteq> 1 
                       \<Longrightarrow> p |\<in>| modelReadyIds m 
                       \<Longrightarrow> p \<noteq> modelStartRid m 
                       \<Longrightarrow> p \<noteq> modelEndRid m
                       \<Longrightarrow> False"
proof -
  fix p
  assume wf_sys: "wf_System sys m"
  assume isRid: "p |\<in>| modelReadyIds m"
  assume notStart: "p \<noteq> modelStartRid m"
  assume notEnd: "p \<noteq> modelEndRid m"
  assume not1: "card {d \<in> dom (nextRel sys). p |\<in>| the (nextRel sys d)} \<noteq> 1"

  \<comment> \<open>the following set is finite\<close>
  from wf_sys have finDom: "finite {d \<in> dom (nextRel sys). p |\<in>| the (nextRel sys d)}"
    by (auto simp add: wf_System_def wf_System_NextRel_def)

  \<comment> \<open>The cardinality of the domain is either 0 or greater that 1\<close>
  from not1 have "card {d \<in> dom (nextRel sys). p |\<in>| the (nextRel sys d)} = 0
        \<or> card {d \<in> dom (nextRel sys). p |\<in>| the (nextRel sys d)} > 1"
    by auto

  then show False
  proof
    assume emptySet: "(card {d \<in> dom (nextRel sys). p |\<in>| the (nextRel sys d)} = 0)"

    \<comment> \<open>There should exist a transition with p as an out place due to the covering requirement
        of the codomain and the model RIDs\<close>
    from wf_sys notStart isRid have "\<exists>d \<in> dom(nextRel sys). p |\<in>| (nextRel sys $ d)"
      apply (simp add: wf_System_def wf_System_NextRel_def wf_System_NextRel_RanUnion_def)
      by blast

    \<comment> \<open>Then there should exist an element in the set\<close>
    from this have "\<exists>x. x \<in> {d \<in> dom (nextRel sys). p |\<in>| the (nextRel sys d)}"
      by auto

    \<comment> \<open>Then the size of the set should be greater than 0\<close>
    from this finDom have "card {d \<in> dom (nextRel sys). p |\<in>| the (nextRel sys d)} > 0"
      using emptySet by auto

    \<comment> \<open>Contradicition\<close>
    from this emptySet show False by simp
  next
    assume bigSet: "card {d \<in> dom (nextRel sys). p |\<in>| the (nextRel sys d)} > 1"

    \<comment> \<open>There should exist at least two distinct elements in the set\<close>
    from bigSet finDom have "\<exists>d1 d2. d1 \<noteq> d2 
                                  \<and> d1 \<in> {d \<in> dom (nextRel sys). p |\<in>| (nextRel sys $ d)}
                                  \<and> d2 \<in> {d \<in> dom (nextRel sys). p |\<in>| (nextRel sys $ d)}"
      by (metis (lifting) card.empty is_singletonI' is_singleton_altdef less_nat_zero_code not1)

    then obtain d1 d2 where d1d2Def: "d1 \<noteq> d2 
                              \<and> d1 \<in> {d \<in> dom (nextRel sys). p |\<in>| (nextRel sys $ d)}
                              \<and> d2 \<in> {d \<in> dom (nextRel sys). p |\<in>| (nextRel sys $ d)}"
      by auto
    from d1d2Def have d1Def: "p |\<in>| (nextRel sys $ d1) \<and> d1 \<in> dom(nextRel sys)"
      by simp
    from d1d2Def have d2Def: "p |\<in>| (nextRel sys $ d2) \<and> d2 \<in> dom(nextRel sys)"
      by simp

    \<comment> \<open>Contradiction since the set of out places  should be disjoint if the in places  are not the same\<close>
    from d1Def d2Def d1d2Def wf_sys show False
      by (auto simp add: wf_System_def wf_System_NextRel_def wf_System_NextRel_DisjointRan_def)
  qed
qed

text \<open>Only one transition should have a place p as an out place\<close>
lemma runNet_Out: "wf_System sys m 
                   \<longrightarrow> (\<forall>p |\<in>| modelReadyIds m - {|modelStartRid m, modelEndRid m|}. 
                          card {d. d \<in> dom(nextRel sys) \<and> p |\<in>| (nextRel sys $ d)} = 1)"
  using runNet_Out' by fastforce

subsubsection \<open>System Helper Functions\<close>

text \<open>System Constructor\<close>
fun mkSystem :: "'value SystemState \<Rightarrow> 'value TaskMap \<Rightarrow> Next \<Rightarrow> RidToTidMap \<Rightarrow> 'value System"
  where "mkSystem init tm next rttm
           = \<lparr>initSystemState = init, taskMap = tm, nextRel = next, activationMap = rttm\<rparr>"

text \<open>Get all Tids of the system\<close>
fun systemTids :: "'store System \<Rightarrow> Tids"
  where "systemTids sys = dom (taskMap sys)"

text \<open>Get all RIDs in the next relation\<close>
fun systemNextRelRids :: "'store System \<Rightarrow> Rid set"
  where "systemNextRelRids sys = (\<Union> (fset ` ((dom (nextRel sys)) \<union> (ran (nextRel sys)))))" 

subsection \<open>SystemState Helper Functions\<close>

text \<open>System Constructor\<close>
definition mkSystemState :: "(Tid, 'a TaskState) map \<Rightarrow> 'a ChState \<Rightarrow> Ready \<Rightarrow> (Tid, 'a TaskState) map \<Rightarrow> 'a ChState \<Rightarrow> 'a SystemState"
  where "mkSystemState sysT sysC r prevSysT prevSysC = 
           \<lparr>systemTasks = sysT, systemChs = sysC, ready = r, previousSystemTasks = prevSysT, previousSystemChs = prevSysC\<rparr>"

subsection \<open>Well-Formedness for SystemStates\<close>

text \<open>Every task in the task map should have a state\<close>

definition wf_SystemState_systemTasks_dom :: "Model \<Rightarrow> 'a SystemState \<Rightarrow> bool"
  where "wf_SystemState_systemTasks_dom m ss \<equiv> dom (systemTasks ss) = (modelTids m)"

text \<open>All task states should be well-formed\<close> 

definition wf_SystemState_systemTasks :: "Model \<Rightarrow> 'a SystemState \<Rightarrow> bool"
  where "wf_SystemState_systemTasks m ss \<equiv>
            \<forall>tid \<in> dom (systemTasks ss).
                wf_TaskState ((modelTaskDescrs m) $ tid) ((systemTasks ss) $ tid)"

text \<open>The schedule state should only deadlock once {|END|} is the schedule state\<close>

definition wf_SystemState_ConditionalDeadlock :: "'a System \<Rightarrow> Model \<Rightarrow> 'a SystemState \<Rightarrow> bool"
  where "wf_SystemState_ConditionalDeadlock sys m st \<equiv> 
      ((ready st) \<noteq> {|(modelEndRid m)|} \<longleftrightarrow> card {s. s |\<subseteq>| (ready st) \<and> s \<in> (dom (nextRel sys))} > 0)"

text \<open>The schedule state of any system state should be reachable from {|START|}\<close>

definition wf_SystemState_Reach :: "'a System \<Rightarrow> Model \<Rightarrow> 'a SystemState \<Rightarrow> bool"
  where "wf_SystemState_Reach sys m ss \<equiv> scheduleReachBody (nextRel sys) {|modelStartRid m|} (ready ss)"

text \<open>All system state schedule states are a subset of the model ready IDs\<close>

definition wf_SystemState_ReadySub :: "'a System \<Rightarrow> Model \<Rightarrow> 'a SystemState \<Rightarrow> bool"
  where "wf_SystemState_ReadySub sys m ss \<equiv> (ready ss) |\<subseteq>| modelReadyIds m"

text "A system state is well formed if the channel state is well formed and all above conditions
      hold true"
definition wf_SystemState :: "Model \<Rightarrow> 'a System \<Rightarrow> 'a SystemState \<Rightarrow> bool"
  where "wf_SystemState m sys ss \<equiv> 
          wf_SystemState_systemTasks_dom m ss
        \<and> wf_SystemState_systemTasks m ss
        \<and> wf_ChState (modelChIds m) (systemChs ss)
        \<and> wf_SystemState_ConditionalDeadlock sys m ss
        \<and> wf_SystemState_Reach sys m ss
        \<and> wf_SystemState_ReadySub sys m ss"

named_theorems wf_SystemState_simps
lemmas [wf_SystemState_simps] =
  wf_SystemState_systemTasks_dom_def
  wf_SystemState_systemTasks_def
  wf_SystemState_ConditionalDeadlock_def
  wf_SystemState_Reach_def
  wf_SystemState_def
  wf_SystemState_ReadySub_def

end
