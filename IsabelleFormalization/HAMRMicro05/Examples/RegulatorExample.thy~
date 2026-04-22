theory RegulatorExample
  imports "../HAMRMicro05ExecutionSemantics" "../HAMRMicro05Model" "../HAMRMicro05Spec"
begin

(* THIS WILL NOT WORK WITH CYCLIC AS THIS ONLY A PART OF THE FULL SYSTEM *)

section \<open>Channels\<close>

text \<open>
''upper_desired_tempWstatus'' := [98..100]      (Table A-5)

''lower_desired_tempWstatus'' := [97..99]       (Table A-5)

''current_tempWstatus'' := [68..105]            (Table A-3)

''upper_desired_temp'' := [98..100]             (Table A-5)

''lower_desired_temp'' := [97..99]              (Table A-5)

''heat_control'' :=                             
      0 = Off
      1 = On

''regulator_mode'' :=
      0 = Init
      1 = Normal
      2 = Failure
\<close>

definition RegCh :: "ChIds"
  where "RegCh = {''upper_desired_tempWstatus'', 
                  ''lower_desired_tempWstatus'', 
                  ''current_tempWstatus'',
                  ''upper_desired_tempWstatus_ad'', 
                  ''lower_desired_tempWstatus_ad'', 
                  ''current_tempWstatus_ad'',
                  ''regulator_mode_logged'',
                  ''upper_desired_temp'', 
                  ''lower_desired_temp'', 
                  ''heat_control'',
                  ''regulator_mode'',
                  ''display_temp''}"

section \<open>Task Description\<close>

text \<open>Admin Component Description\<close>

definition AdminDescr :: "TaskDescr"
  where "AdminDescr = \<lparr>
              inChIds = {''upper_desired_tempWstatus'', ''lower_desired_tempWstatus'', ''current_tempWstatus'', ''regulator_mode''},
              outChIds = {''upper_desired_tempWstatus_ad'', ''lower_desired_tempWstatus_ad'', ''current_tempWstatus_ad'', ''regulator_mode_logged''},
              varIds = {} 
         \<rparr>"

text \<open>All local variables and channels are modified\<close>
definition Admin_lw :: "'value LocalFrame"
  where "Admin_lw inSt outSt \<equiv> True"

text \<open>MRI, MRM, and MHS task states are not modifies and listed channels\<close>
definition Admin_gw :: "'value GlobalFrame"
  where "Admin_gw inSt outSt \<equiv> (fst inSt) $ 2 = (fst outSt) $ 2
                             \<and> (fst inSt) $ 3 = (fst outSt) $ 3
                             \<and> (fst inSt) $ 4 = (fst outSt) $ 4
                             \<and> (snd inSt) $ ''upper_desired_tempWstatus'' = (snd outSt) $ ''upper_desired_tempWstatus'' 
                             \<and> (snd inSt) $ ''lower_desired_tempWstatus'' = (snd outSt) $ ''lower_desired_tempWstatus'' 
                             \<and> (snd inSt) $ ''current_tempWstatus'' = (snd outSt) $ ''current_tempWstatus'' 
                             \<and> (snd inSt) $ ''upper_desired_temp'' = (snd outSt) $ ''upper_desired_temp'' 
                             \<and> (snd inSt) $ ''lower_desired_temp'' = (snd outSt) $ ''lower_desired_temp'' 
                             \<and> (snd inSt) $ ''heat_control'' = (snd outSt) $ ''heat_control'' 
                             \<and> (snd inSt) $ ''regulator_mode'' = (snd outSt) $ ''regulator_mode'' 
                             \<and> (snd inSt) $ ''display_temp'' = (snd outSt) $ ''display_temp''"

text \<open>Manage Regulator Interface Description\<close>

definition MRIDescr :: "TaskDescr"
  where "MRIDescr = \<lparr>
              inChIds = {''upper_desired_tempWstatus_ad'', ''lower_desired_tempWstatus_ad'', ''current_tempWstatus_ad'', ''regulator_mode''},
              outChIds = {''upper_desired_temp'', ''lower_desired_temp'', ''display_temp''},
              varIds = {} 
         \<rparr>" 

text \<open>All local variables and channels are modified\<close>
definition MRI_lw :: "'value LocalFrame"
  where "MRI_lw inSt outSt \<equiv> True"

text \<open>Admin, MRM, and MHS task states are not modifies and listed channels\<close>
definition MRI_gw :: "'value GlobalFrame"
  where "MRI_gw inSt outSt \<equiv> (fst inSt) $ 1 = (fst outSt) $ 1
                             \<and> (fst inSt) $ 3 = (fst outSt) $ 3
                             \<and> (fst inSt) $ 4 = (fst outSt) $ 4 
                             \<and> (snd inSt) $ ''upper_desired_tempWstatus'' = (snd outSt) $ ''upper_desired_tempWstatus''
                             \<and> (snd inSt) $ ''lower_desired_tempWstatus'' = (snd outSt) $ ''lower_desired_tempWstatus'' 
                             \<and> (snd inSt) $ ''current_tempWstatus'' = (snd outSt) $ ''current_tempWstatus'' 
                             \<and> (snd inSt) $ ''upper_desired_tempWstatus_ad'' = (snd outSt) $ ''upper_desired_tempWstatus_ad''
                             \<and> (snd inSt) $ ''lower_desired_tempWstatus_ad'' = (snd outSt) $ ''lower_desired_tempWstatus_ad''
                             \<and> (snd inSt) $ ''current_tempWstatus_ad'' = (snd outSt) $ ''current_tempWstatus_ad''
                             \<and> (snd inSt) $ ''regulator_mode_logged'' = (snd outSt) $ ''regulator_mode_logged''
                             \<and> (snd inSt) $ ''heat_control'' = (snd outSt) $ ''heat_control''
                             \<and> (snd inSt) $ ''regulator_mode'' = (snd outSt) $ ''regulator_mode''"

text \<open>Manage Regulator Mode Description\<close>

definition MRMDescr :: "TaskDescr"
  where "MRMDescr = \<lparr>
              inChIds = {''current_tempWstatus_ad''},
              outChIds = {''regulator_mode''},
              varIds = {} 
         \<rparr>" 

text \<open>All local variables and channels are modified\<close>
definition MRM_lw :: "'value LocalFrame"
  where "MRM_lw inSt outSt\<equiv> True"

text \<open>Admin, MRI, and MHS task states are not modifies and listed channels\<close>
definition MRM_gw :: "'value GlobalFrame"
  where "MRM_gw inSt outSt \<equiv> (fst inSt) $ 1 = (fst outSt) $ 1
                             \<and> (fst inSt) $ 3 = (fst outSt) $ 3
                             \<and> (fst inSt) $ 4 = (fst outSt) $ 4  
                             \<and> (snd inSt) $ ''upper_desired_tempWstatus'' = (snd outSt) $ ''upper_desired_tempWstatus''
                             \<and> (snd inSt) $ ''lower_desired_tempWstatus'' = (snd outSt) $ ''lower_desired_tempWstatus'' 
                             \<and> (snd inSt) $ ''current_tempWstatus'' = (snd outSt) $ ''current_tempWstatus'' 
                             \<and> (snd inSt) $ ''upper_desired_tempWstatus_ad'' = (snd outSt) $ ''upper_desired_tempWstatus_ad''
                             \<and> (snd inSt) $ ''lower_desired_tempWstatus_ad'' = (snd outSt) $ ''lower_desired_tempWstatus_ad''
                             \<and> (snd inSt) $ ''current_tempWstatus_ad'' = (snd outSt) $ ''current_tempWstatus_ad''
                             \<and> (snd inSt) $ ''regulator_mode_logged'' = (snd outSt) $ ''regulator_mode_logged''                             \<and> (snd inSt) $ ''upper_desired_temp'' = (snd outSt) $ ''upper_desired_temp''
                             \<and> (snd inSt) $ ''lower_desired_temp'' = (snd outSt) $ ''lower_desired_temp''
                             \<and> (snd inSt) $ ''heat_control'' = (snd outSt) $ ''heat_control''
                             \<and> (snd inSt) $ ''display_temp'' = (snd outSt) $ ''display_temp''"


text \<open>Manage Heat Source Description\<close>

definition MHSDescr :: "TaskDescr"
  where "MHSDescr = \<lparr>
              inChIds = {''upper_desired_temp'', ''lower_desired_temp'', ''current_tempWstatus_ad'', ''regulator_mode''},
              outChIds = {''heat_control''},
              varIds = {} 
         \<rparr>" 

text \<open>All local variables and channels are modified\<close>
definition MHS_lw :: "'value LocalFrame"
  where "MHS_lw inSt outSt\<equiv> True"

text \<open>Admin, MRI, and MRM task states are not modifies and listed channels\<close>
definition MHS_gw :: "'value GlobalFrame"
  where "MHS_gw inSt outSt \<equiv> (fst inSt) $ 1 = (fst outSt) $ 1
                             \<and> (fst inSt) $ 3 = (fst outSt) $ 3
                             \<and> (fst inSt) $ 4 = (fst outSt) $ 4  
                             \<and> (snd inSt) $ ''upper_desired_tempWstatus'' = (snd outSt) $ ''upper_desired_tempWstatus''
                             \<and> (snd inSt) $ ''lower_desired_tempWstatus'' = (snd outSt) $ ''lower_desired_tempWstatus'' 
                             \<and> (snd inSt) $ ''current_tempWstatus'' = (snd outSt) $ ''current_tempWstatus'' 
                             \<and> (snd inSt) $ ''upper_desired_tempWstatus_ad'' = (snd outSt) $ ''upper_desired_tempWstatus_ad''
                             \<and> (snd inSt) $ ''lower_desired_tempWstatus_ad'' = (snd outSt) $ ''lower_desired_tempWstatus_ad''
                             \<and> (snd inSt) $ ''current_tempWstatus_ad'' = (snd outSt) $ ''current_tempWstatus_ad''
                             \<and> (snd inSt) $ ''regulator_mode_logged'' = (snd outSt) $ ''regulator_mode_logged''
                             \<and> (snd inSt) $ ''regulator_mode'' = (snd outSt) $ ''regulator_mode''
                             \<and> (snd inSt) $ ''upper_desired_temp'' = (snd outSt) $ ''upper_desired_temp''
                             \<and> (snd inSt) $ ''lower_desired_temp'' = (snd outSt) $ ''lower_desired_temp''
                             \<and> (snd inSt) $ ''display_temp'' = (snd outSt) $ ''display_temp''"

text \<open>Write Frame\<close>

definition Reg_writFrame :: "'value WriteFrame"
  where "Reg_writFrame \<equiv> \<lparr>
          lFrame = map_of [(1, Admin_lw), (2, MRI_lw), (3, MRM_lw), (4, MHS_lw)],
          gFrame = map_of [(1, Admin_gw), (2, MRI_gw), (3, MRM_gw), (4, MHS_gw)]
         \<rparr>"

section \<open>Ready Ids\<close>

definition START :: "Rid" where "START = 0"
definition RID_Admin :: "Rid" where "RID_Admin = 1"
definition RID_MRI :: "Rid" where "RID_MRI = 2"
definition RID_MRM :: "Rid" where "RID_MRM = 3"
definition RID_MHS :: "Rid" where "RID_MHS = 4"
definition END :: "Rid" where "END = 5"

definition M1Rids :: "Rids" where "M1Rids = {|START, RID_MRI, RID_MRM, RID_MHS, END|}"

section \<open>Tasks\<close>

text \<open>Admin\<close>

text \<open>This component serves two primary functions:
        1) Act as a log for values from previous cycles e.g. storing the old_regulator mode and previous temperature read off of MRI
        2) Store values read in from the external ports so that reading said ports is consistent\<close>

definition TID_Admin :: "Tid" where "TID_Admin = 1"

definition A_Admin :: "int Action"
  where "A_Admin TSCS = (fst TSCS, (snd TSCS) ++ [''upper_desired_tempWstatus_ad'' \<mapsto> (snd TSCS $ ''upper_desired_tempWstatus''),
                                                  ''lower_desired_tempWstatus_ad'' \<mapsto> (snd TSCS $ ''lower_desired_tempWstatus''),
                                                  ''current_tempWstatus_ad'' \<mapsto> (snd TSCS $ ''current_tempWstatus''),
                                                  ''regulator_mode_logged'' \<mapsto> (snd TSCS $ ''regulator_mode'')])"

definition Task_Admin :: "int Task"
  where "Task_Admin = mkTask TID_Admin A_Admin"

text \<open>Manage Regulator Interface\<close>

definition TID_MRI :: "Tid" where "TID_MRI = 2"

text \<open>The intended behavior of this component is to take the temperatures from
      external ports and pass them to the MHS component. This is a simplification
      of the standard definition of MRI as it does not read in regulate interface
      since displayed_temp and regulator_status are not part of the model, assumes
      that all read in temperatures are valid, and assumes that MRM always returns 
      normal mode.

      MRI also now outputs the current temp that was read in so it can be read in at the start
      of a future schedule cycle\<close>

definition A_MRI :: "int Action" 
  where "A_MRI TSCS = (fst TSCS, (snd TSCS) ++ [''upper_desired_temp'' \<mapsto> (snd TSCS $ ''upper_desired_tempWstatus_ad''),
                                                ''lower_desired_temp'' \<mapsto> (snd TSCS $ ''lower_desired_tempWstatus_ad''),
                                                ''display_temp'' \<mapsto> if (snd TSCS $ ''regulator_mode'') = 1 then (snd TSCS $ ''current_tempWstatus_ad'') else (snd TSCS $ ''display_temp'')])"

definition Task_MRI :: "int Task"
  where "Task_MRI = mkTask TID_MRI A_MRI"

subsection \<open>AC2\<close>

text \<open>Manage Regulator Mode\<close>

definition TID_MRM :: "Tid" where "TID_MRM = 3"

text \<open>The intended behavior of this component is to always return normal mode. This
      is a simplification of the standard definition of MRM as it always returns
      normal mode.\<close>

definition A_MRM :: "int Action" 
  where "A_MRM TSCS =  (fst TSCS, (snd TSCS) ++ [''regulator_mode'' \<mapsto> 1])"

definition Task_MRM :: "int Task"
  where "Task_MRM = mkTask TID_MRM A_MRM"

text \<open>Manage Heat Source\<close>

definition TID_MHS :: "Tid" where "TID_MHS = 4"

text \<open>This intended behavior of this component is to:
        . set the heat_control to on if current_temp < lower_desired_temp 
        . set the heat_control to on if current_temp > upper_desired_temp
        . otherwise default to lastcmd.
      This differs from the standard definition of MHS as it works on the assumption that
      MRM will only put NORMAL_MODE on the regulator_mode port\<close>

definition A_MHS :: "int Action" 
  where "A_MHS TSCS = (if ((snd TSCS) $ ''regulator_mode'' = 1)  
                      then (if ((snd TSCS) $ ''current_tempWstatus_ad'' < (snd TSCS) $ ''lower_desired_temp'') 
                            then (fst TSCS, (snd TSCS) ++ [''heat_control'' \<mapsto> 1]) 
                            else (if ((snd TSCS) $ ''current_tempWstatus_ad'' > (snd TSCS) $ ''upper_desired_temp'')
                                  then (fst TSCS, (snd TSCS) ++ [''heat_control'' \<mapsto> 0]) 
                                  else TSCS))
                      else (fst TSCS, (snd TSCS) ++ [''heat_control'' \<mapsto> 0]))" 

definition Task_MHS :: "int Task"
  where "Task_MHS = mkTask TID_MHS A_MHS"

subsection \<open>Activation Map\<close>

definition RegActivationMap :: "RidToTidMap"
  where "RegActivationMap = map_of [({|START|}, TID_Admin),
                                   ({|RID_MRI|}, TID_MRI),
                                   ({|RID_MRM|}, TID_MRM),
                                   ({|RID_MHS|}, TID_MHS)]"

subsection \<open>Task Map\<close>

definition RegTaskMap :: "int TaskMap"
  where "RegTaskMap = map_of [(TID_Admin, Task_Admin),
                             (TID_MRI, Task_MRI),
                             (TID_MRM, Task_MRM),
                             (TID_MHS, Task_MHS)]"

section \<open>Model\<close>

definition RegModel :: "Model"
  where "RegModel = \<lparr> 
          modelTaskDescrs = map_of [(TID_Admin, AdminDescr),
                                    (TID_MRI, MRIDescr),
                                    (TID_MRM, MRMDescr),
                                    (TID_MHS, MHSDescr)],
          modelChIds = RegCh,
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

definition RegNext :: "Next"
  where "RegNext = map_of [({|START|}, {|RID_MRI|}),
                          ({|RID_MRI|}, {|RID_MRM|}),
                          ({|RID_MRM|}, {|RID_MHS|}),
                          ({|RID_MHS|}, {|END|})]"


section \<open>Initial System State\<close>

text \<open>Admin Initial TaskState\<close>

definition initVarState_Admin :: "int VarState"
  where "initVarState_Admin = map_of []"

definition initTaskState_Admin :: "int TaskState"
  where "initTaskState_Admin = \<lparr>tvar = initVarState_Admin\<rparr>"

text \<open>MRI Initial TaskState\<close>

definition initVarState_MRI :: "int VarState"
  where "initVarState_MRI = map_of []"

definition initTaskState_MRI :: "int TaskState"
  where "initTaskState_MRI = \<lparr>tvar = initVarState_MRI\<rparr>"

text \<open>MRM Initial TaskState\<close>

definition initVarState_MRM :: "int VarState"
  where "initVarState_MRM = map_of []"

definition initTaskState_MRM :: "int TaskState"
  where "initTaskState_MRM = \<lparr>tvar = initVarState_MRM\<rparr>"

text \<open>MHS Initial TaskState\<close>

definition initVarState_MHS :: "int VarState"
  where "initVarState_MHS = map_of []"

definition initTaskState_MHS :: "int TaskState"
  where "initTaskState_MHS = \<lparr>tvar = initVarState_MHS\<rparr>"

text \<open>Initial Channel State\<close>

definition RegInitChState :: "int ChState"
  where "RegInitChState = map_of [(''upper_desired_tempWstatus'', 100), 
                              (''lower_desired_tempWstatus'', 97), 
                              (''current_tempWstatus'', 98),
                              (''upper_desired_tempWstatus_ad'', 100), 
                              (''lower_desired_tempWstatus_ad'', 97), 
                              (''current_tempWstatus_ad'', 97),
                              (''regulator_mode_logged'', 1),
                              (''upper_desired_temp'', 100),
                              (''lower_desired_temp'', 97),
                              (''heat_control'', 0),
                              (''regulator_mode'', 1),
                              (''display_temp'', 97)]"

text \<open>Init System State\<close>

definition RegInitSystemState :: "int SystemState"
  where "RegInitSystemState = \<lparr>
          systemTasks = map_of [(TID_Admin, initTaskState_Admin), (TID_MRI, initTaskState_MRI), (TID_MRM, initTaskState_MRM), (TID_MHS, initTaskState_MHS)],
          systemChs = RegInitChState,
          ready = {|START|},
          previousSystemTasks = map_of [(TID_Admin, initTaskState_Admin), (TID_MRI, initTaskState_MRI), (TID_MRM, initTaskState_MRM), (TID_MHS, initTaskState_MHS)],
          previousSystemChs = RegInitChState
        \<rparr>"

section \<open>System\<close>

definition RegSystem :: "int System"
  where "RegSystem = mkSystem RegInitSystemState RegTaskMap RegNext RegActivationMap"

named_theorems Reg_simps
lemmas [Reg_simps] =
  RegSystem_def
  RegTaskMap_def
  RegNext_def
  RegModel_def
  RegInitSystemState_def
  RegInitChState_def
  initVarState_Admin_def
  initVarState_MRI_def
  initVarState_MRM_def
  initVarState_MHS_def
  initTaskState_Admin_def
  initTaskState_MRI_def
  initTaskState_MRM_def
  initTaskState_MHS_def
  RID_Admin_def
  RID_MRI_def
  RID_MRM_def
  RID_MHS_def
  START_def
  END_def
  TID_Admin_def
  TID_MRI_def
  TID_MRM_def    
  TID_MHS_def
  A_Admin_def
  A_MRI_def
  A_MRM_def
  A_MHS_def
  Task_Admin_def
  Task_MRI_def
  Task_MRM_def
  Task_MHS_def
  RegCh_def
  M1Rids_def
  AdminDescr_def
  MRIDescr_def
  MRMDescr_def
  MHSDescr_def
  RegActivationMap_def
  Reg_writFrame_def
  Admin_lw_def
  MRI_lw_def
  MRM_lw_def
  MHS_lw_def
  Admin_gw_def
  MRI_gw_def
  MRM_gw_def
  MHS_gw_def
  

named_theorems Reg_Tids
lemmas [Reg_Tids] =
  TID_Admin_def
  TID_MRI_def
  TID_MRM_def
  TID_MHS_def

named_theorems Reg_Rids
lemmas [Reg_Rids] =
  RID_Admin_def
  RID_MRI_def
  RID_MRM_def
  RID_MHS_def

section \<open>Well-Formedness of Model, System, and Initial State\<close>

lemma wf_RegModel: "wf_Model RegModel"
  by (auto simp add: Reg_simps wf_Model_simps wf_TaskDescrs_simps initTid_def fcard_def)

lemma wf_M1System: "wf_System RegSystem RegModel"                                                                  
  by (auto simp add: Reg_simps wf_Model_simps wf_TaskDescrs_simps wf_System_simps initTid_def wf 
                     wf_ChState_def card_gt_0_iff fcard_def scheduleReachBody_def 
                     scheduleStepBody_def wf_System_NextRel_SourceAndSink_def)

lemma s1: "{s. s |\<subseteq>| {|0|} \<and> (s = {|0|} \<or> s = {|2|} \<or> s = {|3|} \<or> s = {|4|})} = {{|0|}}"
  by auto

lemma wf_InitSystemState: "wf_SystemState RegModel RegSystem (initSystemState RegSystem)"
  by (auto simp add: Reg_simps wf_Model_simps wf_TaskDescrs_simps wf_System_simps wf_SystemState_simps s1 scheduleReachBody_def wf_TaskState_def wf_ChState_def wf_VarState_dom_def)

subsection TaskContracts

text \<open>Task Admin\<close>

text \<open>No precondition on Admin\<close>

definition RegAdminPre :: "int TaskPre"
  where "RegAdminPre ts cs \<equiv> True"

text \<open>Admin properly logs 
        . ''upper_desired_tempWstatus''
        . ''lower_desired_tempWstatus''
        . ''current_tempWstatus''
        . ''regulator_mode''\<close>
definition RegAdminPost :: "int TaskPost"
  where "RegAdminPost tsPre csPre tsPost csPost \<equiv> (csPost $ ''upper_desired_tempWstatus_ad'') = (csPre $ ''upper_desired_tempWstatus'')
                                                  \<and> (csPost $ ''lower_desired_tempWstatus_ad'') = (csPre $ ''lower_desired_tempWstatus'')
                                                  \<and> (csPost $''current_tempWstatus_ad'') = (csPre $ ''current_tempWstatus'')
                                                  \<and> (csPost $ ''regulator_mode_logged'') = (csPre $ ''regulator_mode'')"

text \<open>Task MRI\<close>

text \<open>The lower temperature desired temp must be less than or equal to the upper desired temp\<close>

definition RegMRIPre :: "int TaskPre"
  where "RegMRIPre ts cs \<equiv> cs $ ''lower_desired_tempWstatus_ad'' \<le> cs $ ''upper_desired_tempWstatus_ad''"

text \<open>
  GUARANTEE: POST ''upper_desired_temp'' = PRE ''upper_desired_tempWstatus_ad''
  GUARANTEE: POST ''lower_desired_temp'' = PRE ''lower_desired_tempWstatus_ad''

  Case 1: if PRE ''regulator_mode'' = 1 then POST ''display_temp'' = PRE ''current_tempWstatus_ad''
  Case 2: if PRE ''regulator_mode'' \<noteq> 1 then POST ''display_temp'' = PRE ''display_temp''
\<close>

definition RegMRIPost :: "int TaskPost"
  where "RegMRIPost tsPre csPre tsPost csPost \<equiv> csPost $ ''upper_desired_temp'' = (csPre $ ''upper_desired_tempWstatus_ad'')
                                                \<and> csPost $ ''lower_desired_temp'' = (csPre $ ''lower_desired_tempWstatus_ad'')
                                                \<and> ((csPre $ ''regulator_mode'') = 1  \<longrightarrow> csPost $ ''display_temp'' = (csPre $ ''current_tempWstatus_ad''))  
                                                \<and> ((csPre $ ''regulator_mode'') \<noteq> 1  \<longrightarrow> csPost $ ''display_temp'' = (csPre $ ''display_temp''))" 
text \<open>Task MRM\<close>

text \<open>No precondition of MRM\<close>

definition RegMRMPre :: "int TaskPre"
  where "RegMRMPre ts cs \<equiv> True"

text \<open>CASE 1: POST ''regulator_mode'' is always 1\<close>

definition RegMRMPost :: "int TaskPost"
  where "RegMRMPost tsPre csPre tsPost csPost \<equiv> csPost $ ''regulator_mode'' = 1"

text \<open>Task MHS\<close>

text \<open>The lower temperature desired temp must be less than or equal to the upper desired temp\<close>

definition RegMHSPre :: "int TaskPre"
  where "RegMHSPre ts cs \<equiv> cs $ ''lower_desired_temp'' \<le> cs $ ''upper_desired_temp''"

text \<open>
  Case 1: if PRE ''regulator_mode'' = 1 and PRE ''current_tempWstatus_ad'' < PRE ''lower_desired_temp''
          then POST ''heat_control'' = 1
  Case 2: if PRE ''regulator_mode'' = 1 and PRE ''current_tempWstatus_ad'' > PRE ''upper_desired_temp''
          then POST ''heat_control'' = 0
  Case 3: if PRE ''regulator_mode'' = 1 
            and PRE ''current_tempWstatus_ad'' \<ge> PRE ''lower_desired_temp''
            and PRE ''current_tempWstatus_ad'' \<le> PRE ''upper_desired_temp''
          then POST ''heat_control'' = PRE ''heat_control''
  Case 4: if PRE ''regulator_mode'' = 0
          then POST ''heat_control'' = 0 
\<close>

definition RegMHSPost :: "int TaskPost"
  where "RegMHSPost tsPre csPre tsPost csPost \<equiv> 
      (csPre $ ''regulator_mode'' = 1 
         \<and> csPre $ ''current_tempWstatus_ad'' < csPre $ ''lower_desired_temp''
         \<longrightarrow> csPost $ ''heat_control'' = 1)
      \<and> (csPre $ ''regulator_mode'' = 1 
         \<and> csPre $ ''current_tempWstatus_ad'' > csPre $ ''upper_desired_temp''
         \<longrightarrow> csPost $ ''heat_control'' = 0)
      \<and> (csPre $ ''regulator_mode'' = 1
         \<and> csPre $ ''current_tempWstatus_ad'' \<ge> csPre $ ''lower_desired_temp'')
         \<and> csPre $ ''current_tempWstatus_ad'' \<le> csPre $ ''upper_desired_temp''
         \<longrightarrow> csPost $ ''heat_control'' = csPre $ ''heat_control''
      \<and> (csPre $ ''regulator_mode'' = 0
         \<longrightarrow> csPost $ ''heat_control'' = 0)"

text \<open>Define the aggregate system contract structure, using the 
individual pieces defined above.\<close>

definition RegTaskPreMap :: "(Tid, int TaskPre) map"
  where "RegTaskPreMap \<equiv>
    map_of [ (TID_Admin, RegAdminPre),
             (TID_MRI, RegMRIPre),
             (TID_MRM, RegMRMPre),
             (TID_MHS, RegMHSPre)]"

definition RegTaskPostMap :: "(Tid, int TaskPost) map"
  where "RegTaskPostMap \<equiv>
    map_of [ (TID_Admin, RegAdminPost),
             (TID_MRI, RegMRIPost),
             (TID_MRM, RegMRMPost),
             (TID_MHS, RegMHSPost)]"

definition RegTaskContracts :: "int TaskContracts"
  where "RegTaskContracts \<equiv> (mkTaskContracts RegTaskPreMap RegTaskPostMap)"

named_theorems RegTaskContracts_simps
lemmas [RegTaskContracts_simps] =
  RegAdminPre_def
  RegAdminPost_def
  RegMRIPre_def
  RegMRIPost_def
  RegMRMPre_def
  RegMRMPost_def
  RegMHSPre_def
  RegMHSPost_def
  RegTaskPreMap_def
  RegTaskPostMap_def
  RegTaskContracts_def

lemma Reg_TaskContracts_wf: "wf_TaskContracts RegSystem RegModel RegTaskContracts"
  by (auto simp add: wf_TaskContracts_def Reg_simps RegTaskContracts_simps wf_TaskContracts_ChState_Pre_def 
                        wf_TaskContracts_ChState_Post_def getTaskChannelState_def applyAction_def getAction_def
                        wf_SystemState_def)
  

section  \<open>System Asserts\<close>

text \<open>if the last regulator mode was normal then displayTemp should equal current temp\<close>

definition Req_REG_DisplayTemp_1 :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool"
  where "Req_REG_DisplayTemp_1 lastRegulatorModePre currentTempWstatus displayTemp \<equiv> 
            (lastRegulatorModePre = 1) \<longrightarrow> displayTemp = currentTempWstatus"

text \<open>if the last regulator mode was not normal than nothing can be guaranteed\<close>

(* This is vacuously true*)

definition Req_REG_DisplayTemp_2 :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool"
  where "Req_REG_DisplayTemp_2 lastRegulatorModePre currentTempWstatus displayTemp \<equiv> 
            (lastRegulatorModePre \<noteq> 1) \<longrightarrow> True"

definition Req_REG_DisplayTemp :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool"
  where "Req_REG_DisplayTemp lastRegulatorModePre currentTempWstatus displayTemp \<equiv>
            Req_REG_DisplayTemp_1 lastRegulatorModePre currentTempWstatus displayTemp
            \<and> Req_REG_DisplayTemp_2 lastRegulatorModePre currentTempWstatus displayTemp"

text \<open>component precondtion\<close>

text \<open>The lower temperature desired temp must be less than or equal to the upper desired temp\<close>

definition Reg_Begin :: "int SystemAssert"
  where "Reg_Begin tst chst \<equiv> chst $ ''lower_desired_tempWstatus'' \<le> chst $ ''upper_desired_tempWstatus''"

text \<open>Display Temperature  precondition\<close>

text \<open>The lower temperature desired temp must be less than or equal to the upper desired temp\<close>

definition DisplayTempRegPre :: "int SystemAssert"
  where "DisplayTempRegPre tst chst \<equiv> chst $ ''lower_desired_tempWstatus'' \<le> chst $ ''upper_desired_tempWstatus''"

text "Admin Post Assertion"

text \<open>
. The lower temperature desired temp must be less than or equal to the upper desired temp
. regulator mode must equal the logged reulator mode
. The current temp read off MRI must equal the logged current temperature
\<close>

definition Admin_Reg_End :: "int SystemAssert"
  where "Admin_Reg_End tst chst \<equiv> chst $ ''lower_desired_tempWstatus_ad'' \<le> chst $ ''upper_desired_tempWstatus_ad''
                          \<and> chst $ ''regulator_mode'' = chst $ ''regulator_mode_logged''
                          \<and> chst $ ''lower_desired_tempWstatus'' \<le> chst $ ''upper_desired_tempWstatus''"

text "MRI Post Assertion"

text \<open>
. The lower temperature desired temp must be less than or equal to the upper desired temp
. The current temp must be equal to the temp put out on the ''current_tempWstatus_MRI'' port
. Req_REG_DisplayTemp as stated above
\<close>

definition MRI_Reg_End :: "int SystemAssert"
  where "MRI_Reg_End tst chst \<equiv> chst $ ''lower_desired_temp'' \<le> chst $ ''upper_desired_temp''
                        \<and> Req_REG_DisplayTemp (chst $ ''regulator_mode_logged'') (chst $ ''current_tempWstatus_ad'') (chst $ ''display_temp'')
                        \<and> chst $ ''lower_desired_tempWstatus'' \<le> chst $ ''upper_desired_tempWstatus''"
                      
text "MRM Post Assertion"

text \<open>
. The lower temperature desired temp must be less than or equal to the upper desired temp
. Req_REG_DisplayTemp as stated above
\<close>

definition MRM_Reg_End :: "int SystemAssert"
  where "MRM_Reg_End tst chst \<equiv> Req_REG_DisplayTemp (chst $ ''regulator_mode_logged'') (chst $ ''current_tempWstatus_ad'') (chst $ ''display_temp'')
                        \<and> chst $ ''lower_desired_temp'' \<le> chst $ ''upper_desired_temp''
                        \<and> chst $ ''lower_desired_tempWstatus'' \<le> chst $ ''upper_desired_tempWstatus''"

text "MHS Post Assertion"

text \<open>
. Req_REG_DisplayTemp as stated above
\<close>

definition MHS_Reg_End :: "int SystemAssert"
  where "MHS_Reg_End tst chst \<equiv> Req_REG_DisplayTemp (chst $ ''regulator_mode_logged'') (chst $ ''current_tempWstatus_ad'') (chst $ ''display_temp'')
                                \<and> chst $ ''lower_desired_temp'' \<le> chst $ ''upper_desired_temp''
                                \<and> chst $ ''lower_desired_tempWstatus'' \<le> chst $ ''upper_desired_tempWstatus''"

text \<open>System Spec\<close>

definition Reg_System_Spec :: "int SystemSpec"
  where "Reg_System_Spec \<equiv> \<lparr>
          sysPlaceAsserts = map_of [(START, DisplayTempRegPre),
                                    (RID_MRI, Admin_Reg_End),
                                    (RID_MRM, MRI_Reg_End),
                                    (RID_MHS, MRM_Reg_End),
                                    (END, MHS_Reg_End)]
        \<rparr>"

named_theorems Reg_spec_simps
lemmas[Reg_spec_simps] =
  Req_REG_DisplayTemp_1_def
  Req_REG_DisplayTemp_2_def
  Req_REG_DisplayTemp_def
  Reg_Begin_def
  DisplayTempRegPre_def
  Admin_Reg_End_def
  MRI_Reg_End_def
  MRM_Reg_End_def
  MHS_Reg_End_def
  

text \<open>To see visual representation of the system go to: 
      https://drive.google.com/file/d/1-u1pXuzir2LJtDMAhSNMcnTe06W_nQ7W/view?usp=sharing\<close>

lemma Reg_System_Spec_wf: "wf_SystemSpec Reg_System_Spec RegSystem"
  by (auto simp add: wf_SystemSpec_def Reg_System_Spec_def Reg_simps)

section \<open>Contract Conformance\<close>

definition Reg_MHIP :: "MayHappenInParallelRel"
  where "Reg_MHIP = {}"

lemma Reg_MHIP_wf: "wf_MayHappenInParallelRel_dom RegSystem Reg_MHIP"
  by (auto simp add: wf_MayHappenInParallelRel_dom_def Reg_MHIP_def Reg_simps)

(* Can be done trivially in practice*)

lemma Reg_MHIP_ind: "mayHappenInParallelInd Reg_MHIP RegSystem Reg_System_Spec"
  by (simp add: mayHappenInParallelInd_def Reg_MHIP_def independent_def)

text \<open>wf Write Frame\<close>

lemma wf_wrf: "wf_WriteFrame RegSystem RegModel Reg_writFrame"
  apply (simp add: Reg_simps)
  apply (simp add: wf_WriteFrame_def wf_WriteFrame_Dom_def)
  apply (simp add: wf_WriteFrame_LocalExec_def wf_WriteFrame_GlobalExec_def)
  apply (simp add: Admin_lw_def Admin_gw_def MRI_lw_def MRI_gw_def MRM_lw_def MRM_gw_def MHS_gw_def MHS_lw_def)
  apply (simp add: applyActionGlobal_def applyAction_def applyActionGlobalAlt_def applyActionAlt_def 
                   getAction_def getTaskChannelStateAlt_def getTaskChannelState_def)
  by (auto simp add: Reg_simps)

text "Complete Contract"

lemma "ContractConformanceVCs RegSystem RegModel RegTaskContracts Reg_System_Spec Reg_MHIP Reg_writFrame"
  (* Clean Up Input For Contracts*)
  apply (simp add: ContractConformanceVCs_def Reg_System_Spec_wf Reg_TaskContracts_wf Reg_MHIP_wf Reg_MHIP_ind wf_wrf)
  apply (intro conjI)
    apply (simp_all add: getPrecedingPlaces_def getFollowingPlaces_def getTid_def Reg_simps getAllTransition_def)
    apply auto
    apply (simp_all add: systemPreTaskVC_def systemNextAssertVC_def taskConVC_def)
    apply (simp_all add: systemPreTaskVCHelper_def applyPrePost_def)
  apply auto
  apply (simp_all add: getTid_def Reg_simps Reg_System_Spec_def getAction_def 
         getTaskChannelState_def applyAction_def applyActionGlobal_def ballAssert_def systemNextAssertVCHelper_skip_def 
         systemNextAssertVCHelper_task_def initStateVC_def)
  apply (simp_all add: Reg_spec_simps Reg_simps RegTaskContracts_simps)
  by(auto simp add: Reg_spec_simps RegTaskContracts_simps)
  
end
