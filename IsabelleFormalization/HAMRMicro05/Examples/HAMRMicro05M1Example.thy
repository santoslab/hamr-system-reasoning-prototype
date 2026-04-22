theory HAMRMicro05M1Example
  imports "../HAMRMicro05ExecutionSemantics" "../HAMRMicro05Model" "../HAMRMicro05Spec"
begin

section \<open>Channels\<close>

text \<open>Available channels: a, b, a1, b1, c\<close>

definition M1Chs :: "ChIds"
  where "M1Chs = {''a'', ''b'', ''a1'', ''b1'', ''c''}"

section \<open>Task Description\<close>

subsection \<open>AC1A Definition\<close>

text\<open>
Task AC1A
  In Channels: b1
  Out Channels: a
  Variables: NONE
\<close>

definition AC1A_Descr :: "TaskDescr" where
"AC1A_Descr = \<lparr>
          inChIds = {''b1''},
          outChIds = {''a''},
          varIds = {} 
        \<rparr>"

text \<open>All local variables and channels are modified\<close>
definition AC1A_lw :: "'value LocalFrame"
  where "AC1A_lw inSt outSt \<equiv> True"

text \<open>AC1B and AC2 task states are not modifies and listed channels\<close>
definition AC1A_gw :: "'value GlobalFrame"
  where "AC1A_gw inSt outSt \<equiv> (fst inSt) $ 2 = (fst outSt) $ 2 
                            \<and> (fst inSt) $ 3 = (fst outSt) $ 3
                            \<and> (snd inSt) $ ''b'' = (snd outSt) $ ''b''
                            \<and> (snd inSt) $ ''a1'' = (snd outSt) $ ''a1''
                            \<and> (snd inSt) $ ''b1'' = (snd outSt) $ ''b1''
                            \<and> (snd inSt) $ ''c'' = (snd outSt) $ ''c''"

subsection \<open>AC1B Definition\<close>

text\<open>
Task AC1B
  In Channels: a1
  Out Channels: b
  Variables: NONE
\<close>

definition AC1B_Descr :: "TaskDescr" where
"AC1B_Descr = \<lparr>
          inChIds = {''a1''},
          outChIds = {''b''},
          varIds = {} 
        \<rparr>"

text \<open>All local variables and channels are modified\<close>
definition AC1B_lw :: "'value LocalFrame"
  where "AC1B_lw inSt outSt \<equiv> True"

text \<open>AC1A and AC2 task states are not modifies and listed channels\<close>
definition AC1B_gw :: "'value GlobalFrame"
  where "AC1B_gw inSt outSt \<equiv> (fst inSt) $ 1 = (fst outSt) $ 1 
                            \<and> (fst inSt) $ 3 = (fst outSt) $ 3
                            \<and> (snd inSt) $ ''a'' = (snd outSt) $ ''a''
                            \<and> (snd inSt) $ ''a1'' = (snd outSt) $ ''a1''
                            \<and> (snd inSt) $ ''b1'' = (snd outSt) $ ''b1''
                            \<and> (snd inSt) $ ''c'' = (snd outSt) $ ''c''"

subsection \<open>AC2 Definition\<close>

text\<open>
Task AC2
  In Channels: a, b
  Out Channels: a1, b1
  Variables: NONE
\<close>

definition AC2_Descr :: "TaskDescr" where
"AC2_Descr = \<lparr>
          inChIds = {''a'', ''b''},
          outChIds = {''a1'', ''b1''},
          varIds = {} 
        \<rparr>"

text \<open>All local variables and channels are modified\<close>
definition AC2_lw :: "'value LocalFrame"
  where "AC2_lw inSt outSt \<equiv> True"

text \<open>AC1A and AC1B task states are not modifies and listed channels\<close>
definition AC2_gw :: "'value GlobalFrame"
  where "AC2_gw inSt outSt \<equiv> (fst inSt) $ 1 = (fst outSt) $ 1 
                             \<and> (fst inSt) $ 2 = (fst outSt) $ 2
                             \<and> (snd inSt) $ ''a'' = (snd outSt) $ ''a''
                             \<and> (snd inSt) $ ''b'' = (snd outSt) $ ''b''
                             \<and> (snd inSt) $ ''c'' = (snd outSt) $ ''c''"

definition M1_writFrame :: "'value WriteFrame"
  where "M1_writFrame \<equiv> \<lparr>
          lFrame = map_of [(1, AC1A_lw), (2, AC1B_lw), (3, AC2_lw)],
          gFrame = map_of [(1, AC1A_gw), (2, AC1B_gw), (3, AC2_gw)]
         \<rparr>"

section \<open>Ready Ids\<close>

definition START :: "Rid" where "START = 0"
definition RID_AC1A :: "Rid" where "RID_AC1A = 1"
definition RID_AC1B :: "Rid" where "RID_AC1B = 2"
definition RID_AC1A_End :: "Rid" where "RID_AC1A_End = 1001"
definition RID_AC1B_End :: "Rid" where "RID_AC1B_End = 1002"
definition RID_AC2 :: "Rid" where "RID_AC2 = 3"
definition END :: "Rid" where "END = 4"

definition M1Rids :: "Rids" where "M1Rids = {|START, RID_AC1A, RID_AC1B, RID_AC1A_End, RID_AC1B_End, RID_AC2, END|}"

section \<open>Tasks\<close>

subsection \<open>AC1A\<close>

definition TID_AC1A :: "Tid" where "TID_AC1A = 1"

text \<open>
AC1A Action:
  ch a := ch b1
\<close>

definition A_AC1A :: "int Action"
  where "A_AC1A TSCS = (fst TSCS,
                       (snd TSCS) ++ [''a'' \<mapsto> (snd TSCS $ ''b1'')])"

definition Task_AC1A :: "int Task"
  where "Task_AC1A = mkTask TID_AC1A A_AC1A"

subsection \<open>AC1B\<close>

definition TID_AC1B :: "Tid" where "TID_AC1B = 2"

text \<open>
AC1B Action:
  ch b := ch a1
\<close>

definition A_AC1B :: "int Action"
  where "A_AC1B TSCS = (fst TSCS,
                       (snd TSCS) ++ [''b'' \<mapsto> (snd TSCS $ ''a1'')])"

definition Task_AC1B :: "int Task"
  where "Task_AC1B = mkTask TID_AC1B A_AC1B"

subsection \<open>AC2\<close>

definition TID_AC2 :: "Tid" where "TID_AC2 = 3"

text \<open>
AC2 Action:
  ch a1 := ch a
  ch b1 := ch b
\<close>

definition A_AC2 :: "int Action"
  where "A_AC2 TSCS = (fst TSCS,
                       (snd TSCS) ++ [''a1'' \<mapsto> (snd TSCS $ ''a''),
                                      ''b1'' \<mapsto> (snd TSCS $ ''b'')])"

definition Task_AC2 :: "int Task"
  where "Task_AC2 = mkTask TID_AC2 A_AC2"

subsection \<open>Activation Map\<close>

definition M1ActivationMap :: "RidToTidMap"
  where "M1ActivationMap = map_of [({|RID_AC1A|}, TID_AC1A),
                                   ({|RID_AC1B|}, TID_AC1B),
                                   ({|RID_AC2|}, TID_AC2)]"

subsection \<open>Task Map\<close>

definition M1TaskMap :: "int TaskMap"
  where "M1TaskMap = map_of [(TID_AC1A, Task_AC1A),
                             (TID_AC1B, Task_AC1B),
                             (TID_AC2, Task_AC2)]"

section \<open>Model\<close>

definition M1Model :: "Model"
  where "M1Model = \<lparr> 
          modelTaskDescrs = map_of [(TID_AC1A, AC1A_Descr),
                                    (TID_AC1B, AC1B_Descr),
                                    (TID_AC2, AC2_Descr)],
          modelChIds = M1Chs,
          modelReadyIds = M1Rids,
          modelStartRid = START,
          modelEndRid = END
        \<rparr>"

section \<open>Next Rel\<close>

text \<open>
M1 Next Relation:
  START \<longrightarrow> RID_AC1A, RID_AC1B
  RID_AC1A \<longrightarrow> RID_AC1A_End
  RID_AC1B \<longrightarrow> RID_AC1B_End
  RID_AC1A_End, RID_AC1B_End \<longrightarrow> RID_AC2
  RID_AC2 \<longrightarrow> END
  END \<longrightarrow> START
\<close>

definition M1Next :: "Next"
  where "M1Next = map_of [({|START|}, {|RID_AC1A, RID_AC1B|}),
                          ({|RID_AC1A|}, {|RID_AC1A_End|}),
                          ({|RID_AC1B|}, {|RID_AC1B_End|}),
                          ({|RID_AC1A_End, RID_AC1B_End|}, {|RID_AC2|}),
                          ({|RID_AC2|}, {|END|})]"


section \<open>Initial System State\<close>

text \<open>AC1A Initial Task State\<close>

definition initVarState_AC1A :: "int VarState"
  where "initVarState_AC1A = map_of []"

definition initTaskState_AC1A :: "int TaskState"
  where "initTaskState_AC1A = \<lparr>tvar = initVarState_AC1A\<rparr>"

text \<open>AC1B Initial Task State\<close>

definition initVarState_AC1B :: "int VarState"
  where "initVarState_AC1B = map_of []"

definition initTaskState_AC1B :: "int TaskState"
  where "initTaskState_AC1B = \<lparr>tvar = initVarState_AC1B\<rparr>"

text \<open>AC2 Initial Task State\<close>

definition initVarState_AC2 :: "int VarState"
  where "initVarState_AC2 = map_of []"

definition initTaskState_AC2 :: "int TaskState"
  where "initTaskState_AC2 = \<lparr>tvar = initVarState_AC2\<rparr>"

text \<open>Initial Channel State\<close>

text \<open>
Initial Channel State:
  ch a := 0
  ch b := 0
  ch a1 := 0
  ch b1 := 1
  ch c := 1
\<close>

definition M1InitChState :: "int ChState"
  where "M1InitChState = map_of [(''a'', 0),
                                 (''b'', 0),
                                 (''a1'', 0),
                                 (''b1'', 1),
                                 (''c'' , 1)]"

text \<open>Init System State\<close>

definition M1InitSystemState :: "int SystemState" 
  where "M1InitSystemState = \<lparr>
          systemTasks = map_of [(TID_AC1A, initTaskState_AC1A), 
                                (TID_AC1B, initTaskState_AC1B), 
                                (TID_AC2, initTaskState_AC2)],
          systemChs = M1InitChState,
          ready = {|START|},
          previousSystemTasks = map_of [(TID_AC1A, initTaskState_AC1A), 
                                        (TID_AC1B, initTaskState_AC1B),   
                                        (TID_AC2, initTaskState_AC2)],
          previousSystemChs = M1InitChState
        \<rparr>"

section \<open>System\<close>

definition M1System :: "int System"
  where "M1System = mkSystem M1InitSystemState M1TaskMap M1Next M1ActivationMap"

named_theorems M1_simps
lemmas [M1_simps] =
  M1System_def
  M1TaskMap_def
  M1Next_def
  M1Model_def
  M1InitSystemState_def
  M1InitChState_def
  initVarState_AC1A_def
  initVarState_AC1B_def
  initVarState_AC2_def
  initTaskState_AC1A_def
  initTaskState_AC1B_def
  initTaskState_AC2_def
  RID_AC1A_End_def
  RID_AC1B_End_def
  RID_AC1A_def
  RID_AC1B_def
  RID_AC2_def
  START_def
  END_def
  TID_AC1A_def
  TID_AC1B_def
  TID_AC2_def
  A_AC1A_def
  A_AC1B_def
  A_AC2_def
  Task_AC1A_def
  Task_AC1B_def
  Task_AC2_def
  M1Chs_def
  M1Rids_def
  AC1A_Descr_def
  AC1B_Descr_def
  AC2_Descr_def
  M1ActivationMap_def
  M1_writFrame_def
  AC1A_lw_def
  AC1A_gw_def
  AC1B_lw_def
  AC1B_gw_def
  AC2_lw_def
  AC2_gw_def
  

named_theorems M1_Tids
lemmas [M1_Tids] =
  TID_AC1A_def
  TID_AC1B_def
  TID_AC2_def

named_theorems M1_Rids
lemmas [M1_Rids] =
  RID_AC1A_End_def
  RID_AC1B_End_def
  RID_AC1A_def
  RID_AC1B_def
  RID_AC2_def

section \<open>Well-Formedness of Model, System, and Initial State\<close>

lemma wf_M1Model: "wf_Model M1Model"
  by (auto simp add: M1_simps wf_Model_simps wf_TaskDescrs_simps initTid_def fcard_def)

lemma wf_M1System: "wf_System M1System M1Model"                                                                  
  by (auto simp add: M1_simps wf_Model_simps wf_TaskDescrs_simps wf_System_simps initTid_def wf 
                     wf_ChState_def card_gt_0_iff fcard_def scheduleReachBody_def 
                     scheduleStepBody_def wf_System_NextRel_SourceAndSink_def)

lemma s1: "{s. s |\<subseteq>| {|0|} \<and> (s = {|0|} \<or> s = {|Suc 0|} \<or> s = {|2|} \<or> s = {|1001, 1002|} \<or> s = {|3|})} = {{|0|}}"
  by fastforce

lemma wf_InitSystemState: "wf_SystemState M1Model M1System (initSystemState M1System)"
  by (auto simp add: M1_simps wf_Model_simps wf_TaskDescrs_simps wf_System_simps wf_SystemState_simps s1 scheduleReachBody_def wf_TaskState_def wf_ChState_def wf_VarState_dom_def)

section \<open>Task Contracts\<close>

text \<open>All contracts are trivial as this example focuses on the system assertions\<close>

definition TID_AC1A_Task_Pre :: "int TaskPre"
  where "TID_AC1A_Task_Pre ts cs \<equiv> True"

text \<open>ch a in the post state should equal channel b1 in the pre state\<close>

definition TID_AC1A_Task_Post :: "int TaskPost"
  where "TID_AC1A_Task_Post ts cs ts' cs' \<equiv> cs' $ ''a'' = cs $ ''b1''"

definition TID_AC1B_Task_Pre :: "int TaskPre"
  where "TID_AC1B_Task_Pre ts cs \<equiv> True"

text \<open>ch b in the post state should equal channel a1 in the pre state\<close>

definition TID_AC1B_Task_Post :: "int TaskPost"
  where "TID_AC1B_Task_Post ts cs ts' cs' \<equiv> cs' $ ''b'' = cs $ ''a1''"

definition TID_AC2_Task_Pre :: "int TaskPre"
  where "TID_AC2_Task_Pre ts cs \<equiv> True"

text \<open>ch a1 in the post state should equal ch a in the pre state and
      ch b1 in the post state should equal ch b in the pre state\<close>

definition TID_AC2_Task_Post :: "int TaskPost"
  where "TID_AC2_Task_Post ts cs ts' cs' \<equiv> cs' $ ''a1'' = cs $ ''a'' \<and> cs' $ ''b1'' = cs $ ''b''"

definition M1_TaskContracts :: "int TaskContracts"
  where "M1_TaskContracts \<equiv> \<lparr>
          taskPre = map_of [(TID_AC1A, TID_AC1A_Task_Pre),
                             (TID_AC1B, TID_AC1B_Task_Pre),
                             (TID_AC2, TID_AC2_Task_Pre)],
          taskPost = map_of [(TID_AC1A, TID_AC1A_Task_Post),
                             (TID_AC1B, TID_AC1B_Task_Post),
                             (TID_AC2, TID_AC2_Task_Post)]\<rparr>"

section  \<open>System Asserts\<close>

text \<open>
START System Assertion:
  ch a1 != ch b1
\<close>

definition START_SysAssert :: "int SystemAssert"
  where "START_SysAssert tst chst \<equiv> (chst $ ''a1'' \<noteq> chst $ ''b1'')"

text \<open>
RID_AC1A System Assertion:
  ch a1 != ch b1
\<close>

definition RID_AC1A_SysAssert :: "int SystemAssert"
  where "RID_AC1A_SysAssert tst chst \<equiv>  (chst $ ''a1'' \<noteq> chst $ ''b1'')"

text \<open>
RID_AC1A_End System Assertion:
  ch a = ch b1
  ch a1 != ch b1
\<close>

definition RID_AC1A_End_SysAssert :: "int SystemAssert"
  where "RID_AC1A_End_SysAssert tst chst \<equiv> chst $ ''a'' =  chst $ ''b1''
                                      \<and> (chst $ ''a1'' \<noteq> chst $ ''b1'')" 

text \<open>
RID_AC1B System Assertion:
  ch a1 != ch b1
\<close>

definition RID_AC1B_SysAssert :: "int SystemAssert"
  where "RID_AC1B_SysAssert tst chst \<equiv>  chst $ ''a1'' \<noteq> chst $ ''b1''"

text \<open>
RID_AC1B_End System Assertion:
  ch b = ch a1
  ch a1 != ch b1
\<close>

definition RID_AC1B_End_SysAssert :: "int SystemAssert"
  where "RID_AC1B_End_SysAssert tst chst \<equiv> chst $ ''b'' =  chst $ ''a1''
                                     \<and> (chst $ ''a1'' \<noteq> chst $ ''b1'')"

text \<open>
RID_AC2 System Assertion:
  ch a1 != ch b1
  ch a = ch b1
  ch b = ch a1
\<close>

definition RID_AC2_SysAssert :: "int SystemAssert"
  where "RID_AC2_SysAssert tst chst \<equiv> (chst $ ''a1'' \<noteq> chst $ ''b1'')
                                   \<and> (chst $ ''a'' = chst $ ''b1'')
                                   \<and> (chst $ ''b'' = chst $ ''a1'')"

text \<open>
END System Assertion:
  ch a1 != ch b1
  ch a1 = ch a
  ch b1 = ch b
\<close>

definition END_SysAssert :: "int SystemAssert"
  where "END_SysAssert tst chst \<equiv> (chst $ ''a1'' \<noteq> chst $ ''b1'')
                                   \<and> (chst $ ''a1'' = chst $ ''a'')
                                   \<and> (chst $ ''b1'' = chst $ ''b'')"

definition M1_System_Spec :: "int SystemSpec"
  where "M1_System_Spec \<equiv> \<lparr>
          sysPlaceAsserts = map_of [(START, START_SysAssert),
                                    (RID_AC1A, RID_AC1A_SysAssert),
                                    (RID_AC1A_End, RID_AC1A_End_SysAssert),
                                    (RID_AC1B, RID_AC1B_SysAssert),
                                    (RID_AC1B_End, RID_AC1B_End_SysAssert),
                                    (RID_AC2, RID_AC2_SysAssert),
                                    (END, END_SysAssert)]
        \<rparr>"

named_theorems M1_spec_simps
lemmas[M1_spec_simps] =
  TID_AC1A_Task_Pre_def
  TID_AC1A_Task_Post_def
  TID_AC1B_Task_Pre_def
  TID_AC1B_Task_Post_def
  TID_AC2_Task_Pre_def
  TID_AC2_Task_Post_def
  M1_TaskContracts_def
  RID_AC1A_SysAssert_def
  RID_AC1A_End_SysAssert_def
  RID_AC1B_SysAssert_def
  RID_AC1B_End_SysAssert_def
  RID_AC2_SysAssert_def
  M1_System_Spec_def
  START_SysAssert_def
  END_SysAssert_def



lemma M1_TaskContracts_wf: "wf_TaskContracts M1System M1Model M1_TaskContracts"
  by (auto simp add: wf_TaskContracts_def M1_simps M1_spec_simps wf_TaskContracts_ChState_Pre_def 
                        wf_TaskContracts_ChState_Post_def getTaskChannelState_def applyAction_def getAction_def
                        wf_SystemState_def)
  

text \<open>To see visual representation of the system go to: 
      https://drive.google.com/file/d/1-u1pXuzir2LJtDMAhSNMcnTe06W_nQ7W/view?usp=sharing\<close>

lemma M1_System_Spec_wf: "wf_SystemSpec M1_System_Spec M1System"
  by (auto simp add: wf_SystemSpec_def M1_System_Spec_def M1_simps)

section \<open>Contract Conformance\<close>

text \<open>MHIP set\<close>
definition M1_MHIP :: "MayHappenInParallelRel"
  where "M1_MHIP = {({|RID_AC1A|}, {|RID_AC1B|})}"

text \<open>MHIP is well formed\<close>
lemma M1_MHIP_wf: "wf_MayHappenInParallelRel_dom M1System M1_MHIP"
  by (auto simp add: wf_MayHappenInParallelRel_dom_def M1_MHIP_def M1_simps)

(* Can be done trivially in practice*)

text \<open>Every pair of transitions in MHIP are independent\<close>
lemma M1_MHIP_ind: "mayHappenInParallelInd M1_MHIP M1System M1_System_Spec"
  apply (simp add: mayHappenInParallelInd_def M1_MHIP_def independent_def)
  apply (rule conjI)
   apply (simp add: execIndependent_def M1_simps)
   apply (auto simp add: applyActionGlobalComp_def applyActionGlobalAlt_def applyActionGlobal_def applyAction_def getAction_def getTid_def M1_simps getTaskChannelState_def applyActionAlt_def getTaskChannelStateAlt_def ballAssert_def M1_spec_simps)
  apply (simp add: nonBlocking_def M1_simps)
  apply (simp add: applyActionGlobalComp_def applyActionGlobalAlt_def applyActionGlobal_def applyAction_def getAction_def getTid_def M1_simps getTaskChannelState_def applyActionAlt_def getTaskChannelStateAlt_def)
  apply (auto simp add: M1_spec_simps M1_simps)
   apply (simp add: ballAssert_def ballAssertAlt_def)
   apply (simp add: RID_AC1A_SysAssert_def RID_AC1B_SysAssert_def)
   apply (simp add: ballAssert_def ballAssertAlt_def)
   apply (simp add: RID_AC1A_SysAssert_def RID_AC1B_SysAssert_def)
  apply (simp add: nonContradictPost_def M1_simps)
  apply (simp add: applyActionGlobalComp_def applyActionGlobalAlt_def applyActionGlobal_def applyAction_def getAction_def getTid_def M1_simps getTaskChannelState_def applyActionAlt_def getTaskChannelStateAlt_def)
   apply (simp add: ballAssert_def ballAssertAlt_def)
   apply (simp add: RID_AC1A_SysAssert_def RID_AC1B_End_SysAssert_def RID_AC1A_End_SysAssert_def)
  done

text \<open>systemPreTaskVC\<close>
  
lemma fold1: "\<forall>x. (\<exists>r. x =
             the (if r = 0 then Some START_SysAssert
                        else [4 \<mapsto> END_SysAssert, 3 \<mapsto> RID_AC2_SysAssert, 1002 \<mapsto> RID_AC1B_End_SysAssert,
                              2 \<mapsto> RID_AC1B_SysAssert, 1001 \<mapsto> RID_AC1A_End_SysAssert, Suc 0 \<mapsto> RID_AC1A_SysAssert]
                              r)
              (systemTasks st) (systemChs st) \<and>
             (r = 1001 \<or> r = 1002)) \<longrightarrow>
        x
        \<equiv> RID_AC1A_End_SysAssert (systemTasks st) (systemChs st) \<and> RID_AC1B_End_SysAssert (systemTasks st) (systemChs st)"
  apply (simp add: M1_simps M1_spec_simps)
  by (smt (verit) RID_AC1A_End_SysAssert_def RID_AC1B_End_SysAssert_def fun_upd_apply numeral_1_eq_Suc_0 numeral_eq_iff
      option.sel semiring_norm(85,86,87,89) zero_neq_numeral)

text \<open>wf Write Frame\<close>

lemma wf_wrf: "wf_WriteFrame M1System M1Model M1_writFrame"
  by (auto simp add: M1_simps wf_WriteFrame_simps applyActionGlobalAlt_def applyActionAlt_def 
                     getAction_def getTaskChannelStateAlt_def applyActionGlobal_def applyAction_def
                     getTaskChannelState_def)

text "Complete Contract"

lemma "ContractConformanceVCs M1System M1Model M1_TaskContracts M1_System_Spec M1_MHIP M1_writFrame"
  (* Clean Up Input For Contracts*)
  apply (simp add: ContractConformanceVCs_def M1_System_Spec_wf M1_TaskContracts_wf M1_MHIP_wf M1_MHIP_ind wf_wrf)
  apply (intro conjI)
    apply (simp_all add: getPrecedingPlaces_def getFollowingPlaces_def getTid_def M1_simps getAllTransition_def)
    apply auto
    apply (simp_all add: systemPreTaskVC_def systemNextAssertVC_def taskConVC_def postPreAssertVC_def)
    apply (simp_all add: systemPreTaskVCHelper_def systemNextAssertVCHelper_skip_def applyPrePost_def)
  apply auto
  apply (simp_all add: getTid_def M1_simps fold1 M1_System_Spec_def M1_TaskContracts_def getAction_def 
                       getTaskChannelState_def applyAction_def applyActionGlobal_def ballAssert_def
                       initStateVC_def systemNextAssertVCHelper_task_def)
  by (simp_all add: M1_spec_simps M1_simps)
  
end
