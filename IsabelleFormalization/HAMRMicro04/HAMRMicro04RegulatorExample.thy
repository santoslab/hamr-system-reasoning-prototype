theory HAMRMicro04RegulatorExample
  imports HAMRMicro04ExecutionSemantics HAMRMicro04Model HAMRMicro04Spec
begin

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

section \<open>Task Descriptions\<close>

text \<open>Admin Component Description\<close>

definition AdminDescr :: "TaskDescr"
  where "AdminDescr = \<lparr>
              inChIds = {''upper_desired_tempWstatus'', ''lower_desired_tempWstatus'', ''current_tempWstatus'', ''regulator_mode''},
              outChIds = {''upper_desired_tempWstatus_ad'', ''lower_desired_tempWstatus_ad'', ''current_tempWstatus_ad'', ''regulator_mode_logged''},
              varIds = {} 
         \<rparr>" 

text \<open>Manage Regulator Interface Description\<close>

definition MRIDescr :: "TaskDescr"
  where "MRIDescr = \<lparr>
              inChIds = {''upper_desired_tempWstatus_ad'', ''lower_desired_tempWstatus_ad'', ''current_tempWstatus_ad'', ''regulator_mode''},
              outChIds = {''upper_desired_temp'', ''lower_desired_temp'', ''display_temp''},
              varIds = {} 
         \<rparr>" 

text \<open>Manage Regulator Mode Description\<close>

definition MRMDescr :: "TaskDescr"
  where "MRMDescr = \<lparr>
              inChIds = {''current_tempWstatus_ad''},
              outChIds = {''regulator_mode''},
              varIds = {} 
         \<rparr>" 
 
text \<open>Manage Heat Source Description\<close>

definition MHSDescr :: "TaskDescr"
  where "MHSDescr = \<lparr>
              inChIds = {''upper_desired_temp'', ''lower_desired_temp'', ''current_tempWstatus_ad'', ''regulator_mode''},
              outChIds = {''heat_control''},
              varIds = {} 
         \<rparr>" 

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

text \<open>Task Map\<close>

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
          modelChIds = RegCh
        \<rparr>"

section \<open>Schedule\<close>

definition RegSchedule :: "Schedule"
  where "RegSchedule = [TID_Admin, TID_MRI, TID_MRM, TID_MHS]"

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

definition RegInitChState :: "(int) ChState"
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
          scheduleState = initScheduleState RegSchedule,
          previousSystemTasks = map_of [(TID_Admin, initTaskState_Admin), (TID_MRI, initTaskState_MRI), (TID_MRM, initTaskState_MRM), (TID_MHS, initTaskState_MHS)],
          previousSystemChs = RegInitChState
        \<rparr>"

section \<open>System\<close>

definition RegSystem :: "int System"
  where "RegSystem = mkSystem RegInitSystemState RegTaskMap RegSchedule"

section \<open>Well Formedness\<close>

named_theorems Reg_simps
lemmas [Reg_simps] =
  RegSystem_def
  RegTaskMap_def
  RegSchedule_def
  RegModel_def
  RegInitSystemState_def
  RegInitChState_def
  initVarState_Admin_def
  initTaskState_Admin_def
  initVarState_MHS_def
  initTaskState_MHS_def
  initVarState_MRI_def
  initTaskState_MRI_def
  initVarState_MRM_def
  initTaskState_MRM_def
  TID_Admin_def
  A_Admin_def
  Task_Admin_def
  TID_MHS_def
  A_MHS_def
  Task_MHS_def
  TID_MRI_def
  A_MRI_def
  Task_MRI_def
  TID_MRM_def
  A_MRM_def
  Task_MRM_def
  RegCh_def
  AdminDescr_def
  MRIDescr_def
  MRMDescr_def
  MHSDescr_def

lemma wf_RegModel: "wf_Model RegModel"             
  by (auto simp add: Reg_simps wf_Model_simps wf_TaskDescrs_simps initTid_def)
  
lemma wf_RegSystem: "wf_System RegSystem RegModel"
  by (auto simp add: Reg_simps wf_Model_simps wf_TaskDescrs_simps wf_System_simps  initTid_def wf_ChState_def)

lemma wf_InitSystemState: "wf_SystemState RegModel RegSystem (initSystemState RegSystem)"
  by (auto simp add: Reg_simps wf_Model_simps wf_TaskDescrs_simps wf_System_simps wf_SystemState_simps wf_TaskState_def wf_ChState_def wf_VarState_dom_def wf_ScheduleState_simps)

section \<open>Specification\<close>

subsection \<open>Schedule Contract\<close>

text \<open>Next, we establish the set of actions that the system
could execute in a single step.\<close>

lemma RegSystem_scheduleNext_cases: 
  assumes wf_ScheduleState: "wf_ScheduleState RegSystem schst" 
     and scheduleNext: "scheduleNext (schedule RegSystem) schst = schst'"
   shows "currTid schst' = TID_MRI \<or> currTid schst' = TID_MRM \<or> currTid schst' = TID_MHS \<or> currTid schst' = TID_Admin"
proof - 
  from  wf_RegSystem wf_ScheduleState scheduleNext 
  have tids_in_system: "currTid schst' \<in> systemTids RegSystem" 
    using scheduleNext_preserves_wf wf_ScheduleState_currTid_inSys_def wf_RegModel by blast   
  from tids_in_system show ?thesis by (auto simp add: Reg_simps)
qed

text \<open>Thus, the result of a step always produces a state with currTid in the systemTids.
   That is, currTid is never the initTid.   This will let us conclude that
   the initTid only occurs in the initial state.\<close>

lemma RegSystem_systemStep_cases: 
  assumes wf_SystemState: "wf_SystemState RegModel RegSystem st1"
      and step: "systemStep RegSystem st1 st2"
  shows "(((systemTasks st2) $ (currTidSystemState st2), systemChs st2) = (do_action ((systemTasks st1) $ (nextTidSystemState RegSystem st1), systemChs st1) A_MRI)
     \<or>   ((systemTasks st2) $ (currTidSystemState st2), systemChs st2) = (do_action ((systemTasks st1) $ (nextTidSystemState RegSystem st1), systemChs st1) A_MRM)
     \<or>   ((systemTasks st2) $ (currTidSystemState st2), systemChs st2) = (do_action ((systemTasks st1) $ (nextTidSystemState RegSystem st1), systemChs st1) A_MHS)
     \<or>   ((systemTasks st2) $ (currTidSystemState st2), systemChs st2) = (do_action ((systemTasks st1) $ (nextTidSystemState RegSystem st1), systemChs st1) A_Admin)
      )"
proof -
 \<comment> \<open>Name the intermediate elements of a system step\<close>
  obtain systemTasks1 systemChs1 taskState' tid tidAction tscs scheduleState2 systemTasks2 systemChs2 where
    p0: "systemTasks1 = systemTasks st1" and
    p1: "systemChs1 = systemChs st1" and
    p2: "scheduleState2 = scheduleNext (schedule RegSystem) (scheduleState st1)" and
    p2a: "tid = (currTid scheduleState2)" and
    p3: "tidAction = action ((taskMap RegSystem) $ tid)" and
    p4: "taskState' = systemTasks1 $ tid" and
    p5: "tscs = do_action (taskState', systemChs1) tidAction" and
    p5a: "systemTasks2 = systemTasks1 (tid \<mapsto> fst tscs)" and
    p5b: "systemChs2 = snd tscs" and
    p6: "st2 = mkSystemState systemTasks2 systemChs2 scheduleState2 systemTasks1 systemChs1"
    using step
    by (metis systemStep.simps)
  from  wf_RegSystem wf_RegModel wf_SystemState p2 p2a
  have currTid2_in_Ex1: "tid \<in> systemTids RegSystem" 
    using wf_SystemState_def 
          scheduleNext_preserves_wf 
          wf_ScheduleState_currTid_inSys_def
    by blast
  \<comment> \<open>Therefore, looking up the tid in the task action structure will yield
  an action that is part of the system.\<close>
  from currTid2_in_Ex1 p3 
  have action_cases: "tidAction = A_MRI \<or> tidAction = A_MRM \<or> tidAction = A_MHS \<or> tidAction = A_Admin" 
    by (auto simp add: Reg_simps)
  from action_cases p5 p6 show ?thesis
    by (metis SystemState.select_convs(1,2,3) currTidSystemState.simps fun_upd_def mkSystemState_def nextTidSystemState.simps option.sel p0 p1 p2 p2a p4 p5a p5b prod.collapse) 
qed

subsection \<open>Regulator Properties\<close>

text \<open>Define a scheduling contract.\<close>

definition RegMayFollow :: "ScheduleMayFollow" where
"RegMayFollow \<equiv>
  mkCRel{(initTid, TID_Admin),
   (TID_Admin, TID_MRI),
   (TID_MRI, TID_MRM),
   (TID_MRM, TID_MHS),
   (TID_MHS, TID_Admin)}"

definition RegScheduleContract :: "ScheduleContracts" where
  "RegScheduleContract \<equiv> mkScheduleContracts RegMayFollow"

named_theorems Reg_ScheduleContract_simps
lemmas [Reg_ScheduleContract_simps] =
  RegMayFollow_def
  RegScheduleContract_def

lemma RegScheduleContracts_wf: "wf_ScheduleContracts RegSystem RegScheduleContract"
  by (auto simp add: wf_ScheduleContracts_def Reg_simps Reg_ScheduleContract_simps)

text \<open>Show that the scheduling contract above satisfies framework verification
conditions, i.e., show that the task order indicated by the scheduling contract
is a sound abstraction of the actual task scheduling.\<close>


lemma Reg_ScheduleContractsVC:
  "ScheduleContractsVC RegSystem RegModel RegScheduleContract"
  unfolding ScheduleContractsVC_def
  apply clarify
proof -
  fix schst
  assume wf_sys: "wf_System RegSystem RegModel"
  assume wf_schons: "wf_ScheduleContracts RegSystem RegScheduleContract"
  assume wf_schst: "wf_ScheduleState RegSystem schst"
  from wf_schst have slotNumRange: "0 \<le> (nextSlotNum schst) \<and> (nextSlotNum schst) < (length (schedule RegSystem))"
    unfolding wf_ScheduleState_def wf_ScheduleState_nextSlotNum_def by blast
  from slotNumRange have slotNumValues: "nextSlotNum schst \<in> {0,1,2,3}"
    by (auto simp add: Reg_simps)
  show "mayFollow RegScheduleContract (currTid schst) (currTid (scheduleNext (schedule RegSystem) schst))"
    using slotNumValues
    using wf_schst apply (auto simp add: wf_ScheduleState_simps Reg_ScheduleContract_simps Reg_simps)
    done
qed

subsection TaskContracts

text \<open>initPost\<close>

definition RegInitPost :: "int TaskState \<Rightarrow> int ChState \<Rightarrow> bool"
  where "RegInitPost ts cs \<equiv> True"

text \<open>Task Admin\<close>

text \<open>No precondition on Admin\<close>

definition RegAdminPre :: "int TaskState \<Rightarrow> int ChState \<Rightarrow> bool"
  where "RegAdminPre ts cs \<equiv> True"

definition RegAdminPost :: "int TaskState \<Rightarrow> int ChState \<Rightarrow> int TaskState \<Rightarrow> int ChState \<Rightarrow> bool"
  where "RegAdminPost tsPre csPre tsPost csPost \<equiv> True"

text \<open>Task MRI\<close>

text \<open>The lower temperature desired temp must be less than or equal to the upper desired temp\<close>

definition RegMRIPre :: "int TaskState \<Rightarrow> int ChState \<Rightarrow> bool"
  where "RegMRIPre ts cs \<equiv> cs $ ''lower_desired_tempWstatus_ad'' \<le> cs $ ''upper_desired_tempWstatus_ad''"

definition RegMRIPost :: "int TaskState \<Rightarrow> int ChState \<Rightarrow> int TaskState \<Rightarrow> int ChState \<Rightarrow> bool"
  where "RegMRIPost tsPre csPre tsPost csPost \<equiv> True"

text \<open>Task MRM\<close>

text \<open>No precondition of MRM\<close>

definition RegMRMPre :: "int TaskState \<Rightarrow> int ChState \<Rightarrow> bool"
  where "RegMRMPre ts cs \<equiv> True"

definition RegMRMPost :: "int TaskState \<Rightarrow> int ChState \<Rightarrow> int TaskState \<Rightarrow> int ChState \<Rightarrow> bool"
  where "RegMRMPost tsPre csPre tsPost csPost \<equiv> True"

text \<open>Task MHS\<close>

text \<open>The lower temperature desired temp must be less than or equal to the upper desired temp\<close>

definition RegMHSPre :: "int TaskState \<Rightarrow> int ChState \<Rightarrow> bool"
  where "RegMHSPre ts cs \<equiv> cs $ ''lower_desired_temp'' \<le> cs $ ''upper_desired_temp''"

definition RegMHSPost :: "int TaskState \<Rightarrow> int ChState \<Rightarrow> int TaskState \<Rightarrow> int ChState \<Rightarrow> bool"
  where "RegMHSPost tsPre csPre tsPost csPost \<equiv> True"

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
  where "RegTaskContracts \<equiv> (mkTaskContracts RegInitPost RegTaskPreMap RegTaskPostMap)"

named_theorems RegTaskContracts_simps
lemmas [RegTaskContracts_simps] =
  RegInitPost_def
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

text \<open>Task Contract Well-Formedness\<close>

lemma RegTaskContracts_wf:
  "wf_TaskContracts RegSystem RegTaskContracts"
  by (simp add: wf_TaskContracts_def Reg_simps RegTaskContracts_simps)

subsection \<open>Component Specification\<close>

text \<open>Task Ordering\<close>

text \<open>Ordering: Admin --> MRI --> MRM --> MHS\<close>

definition RegSubSystemTaskOrdering :: "TaskOrdering" where
"RegSubSystemTaskOrdering \<equiv>
  mkCRel{ (TID_Admin, TID_MRI),
          (TID_MRI, TID_MRM),
          (TID_MRM, TID_MHS)}"

text \<open>Helper Definition\<close>

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

definition Reg_Begin :: "int SystemState \<Rightarrow> bool"
  where "Reg_Begin st \<equiv> (systemChs st) $ ''lower_desired_tempWstatus'' \<le> (systemChs st) $ ''upper_desired_tempWstatus''"

text \<open>Display Temperature  precondition\<close>

text \<open>The lower temperature desired temp must be less than or equal to the upper desired temp\<close>

definition DisplayTempRegPre :: "int SystemState \<Rightarrow> bool"
  where "DisplayTempRegPre st \<equiv> (systemChs st) $ ''lower_desired_tempWstatus'' \<le> (systemChs st) $ ''upper_desired_tempWstatus''"

text "Admin Post Assertion"

text \<open>
. The lower temperature desired temp must be less than or equal to the upper desired temp
. regulator mode must equal the logged reulator mode
. The current temp read off MRI must equal the logged current temperature
\<close>

(* Do not need to log MRI *)

definition Admin_Reg_End :: "int SystemState \<Rightarrow> bool"
  where "Admin_Reg_End st \<equiv> (systemChs st) $ ''lower_desired_tempWstatus_ad'' \<le> (systemChs st) $ ''upper_desired_tempWstatus_ad''
                          \<and> (systemChs st) $ ''regulator_mode'' = (systemChs st) $ ''regulator_mode_logged''"

text "MRI Post Assertion"

text \<open>
. The lower temperature desired temp must be less than or equal to the upper desired temp
. The current temp must be equal to the temp put out on the ''current_tempWstatus_MRI'' port
. Req_REG_DisplayTemp as stated above
\<close>

definition MRI_Reg_End :: "int SystemState \<Rightarrow> bool"
  where "MRI_Reg_End st \<equiv> (systemChs st) $ ''lower_desired_temp'' \<le> (systemChs st) $ ''upper_desired_temp''
                        \<and> Req_REG_DisplayTemp ((systemChs st) $ ''regulator_mode_logged'') ((systemChs st) $ ''current_tempWstatus_ad'') ((systemChs st) $ ''display_temp'')"
                      
text "MRM Post Assertion"

text \<open>
. The lower temperature desired temp must be less than or equal to the upper desired temp
. Req_REG_DisplayTemp as stated above
\<close>

definition MRM_Reg_End :: "int SystemState \<Rightarrow> bool"
  where "MRM_Reg_End st \<equiv> Req_REG_DisplayTemp ((systemChs st) $ ''regulator_mode_logged'') ((systemChs st) $ ''current_tempWstatus_ad'') ((systemChs st) $ ''display_temp'')
                        \<and> (systemChs st) $ ''lower_desired_temp'' \<le> (systemChs st) $ ''upper_desired_temp''"

text "MHS Post Assertion"

text \<open>
. Req_REG_DisplayTemp as stated above
\<close>

definition MHS_Reg_End :: "int SystemState \<Rightarrow> bool"
  where "MHS_Reg_End st \<equiv> Req_REG_DisplayTemp ((systemChs st) $ ''regulator_mode_logged'') ((systemChs st) $ ''current_tempWstatus_ad'') ((systemChs st) $ ''display_temp'')"

text "Combined Post Assert"

definition Reg_End :: "(Tid, int SystemAssert) map"
  where "Reg_End \<equiv>
          map_of [(TID_Admin, Admin_Reg_End),
                 (TID_MRI, MRI_Reg_End),
                 (TID_MRM, MRM_Reg_End),
                 (TID_MHS, MHS_Reg_End)]"

text \<open>Display Temperature postcondition\<close>

text \<open>
. Req_REG_DisplayTemp as stated above
\<close>

definition DisplayTempRegPost :: "int SystemState \<Rightarrow> bool"
  where "DisplayTempRegPost st \<equiv> Req_REG_DisplayTemp ((systemChs st) $ ''regulator_mode_logged'') ((systemChs st) $ ''current_tempWstatus_ad'') ((systemChs st) $ ''display_temp'')"

text \<open>Regulator Subsystem Specification\<close>

definition RegSysSpec :: "int SystemSpec"
  where "RegSysSpec \<equiv> mkSysSpec RegSubSystemTaskOrdering Reg_Begin DisplayTempRegPre Reg_End DisplayTempRegPost"

named_theorems RegSysSpec_simps
lemmas [RegSysSpec_simps] =
  RegSubSystemTaskOrdering_def
  Reg_Begin_def
  DisplayTempRegPre_def
  Admin_Reg_End_def
  MRI_Reg_End_def
  MRM_Reg_End_def
  MHS_Reg_End_def
  Reg_End_def
  DisplayTempRegPost_def
  RegSysSpec_def
  

text "Subsystem Specification Well-Formedness"

lemma reduce1: "{a. \<exists>b. a = Suc 0 \<and> b = 2 \<or> a = 2 \<and> b = 3 \<or> a = 3 \<and> b = 4} = {1, 2, 3}"
  by auto

lemma reduce2: "{b. \<exists>a. a = Suc 0 \<and> b = 2 \<or> a = 2 \<and> b = 3 \<or> a = 3 \<and> b = 4} = {2, 3, 4}"
  by auto

lemma RegSubSysSpec_wf: "wf_SystemSpec RegSysSpec RegSystem RegScheduleContract"
  by (auto simp add: reduce1 reduce2 RegSysSpec_simps Reg_simps wf_SystemSpec_simps 
                     TaskOrdering_simps Reg_ScheduleContract_simps mkSysSpec_def)

(* ---------------- PreVC ---------------- *)

(* 
   At the moment, Precondition VCs are relatively consistent in how they are proven with a 
   very consistent pattern that has been used in both this example and the pythagTriple
   example 
*)

text \<open>Display Temp Function Precondition VC: 
        Regulator Pre Condition -> Display Temp Function Precondition\<close>

lemma DisplayTempPreVC: "funPreVC RegSystem RegSysSpec st"
  by (auto simp add: funPreVC_def mkSysSpec_def RegSysSpec_simps)

text \<open>Admin Precondition VC:
        Display Temp Function Precondition -> Admin Task Precondition\<close>

lemma RegAdminPre_sat: "startPreVC RegSystem RegSysSpec RegTaskContracts st TID_Admin"
  by (auto simp add: startPreVC_def mkSysSpec_def RegSysSpec_simps RegTaskContracts_simps)

text \<open>MRI Precondition VC:
        Admin_End /\ True -> MRI Precondition\<close>

lemma RegMRIPre_sat: "taskPreSysVC RegSystem RegSysSpec RegTaskContracts st TID_MRI"
  unfolding taskPreSysVC_def
proof (auto simp add: RegTaskContracts_def TID_MRI_def RegTaskPreMap_def TID_Admin_def)
  assume a1: "foldPostAssert RegSysSpec st 2" \<comment> \<open>folding of the post assertions directly preceding MRI\<close>

  from a1 have conjPost: "Admin_Reg_End st" \<comment> \<open>proving what the conjunction of the directly preceding post assertions are\<close>
    by (simp add: Reg_simps RegSysSpec_simps foldPostAssert_def mkSysSpec_def)

  from conjPost show "RegMRIPre (the (systemTasks st 2)) (systemChs st)"
    by (simp add: RegSysSpec_simps RegMRIPre_def)
qed

text \<open>MRM Precondition VC:
        MRI_End /\ True -> MRM Precondition\<close>

lemma RegMRMPre_sat: "taskPreSysVC RegSystem RegSysSpec RegTaskContracts st TID_MRM"
  unfolding taskPreSysVC_def
proof (auto simp add: RegTaskContracts_def TID_MRM_def RegTaskPreMap_def TID_Admin_def TID_MRI_def)
  assume a1: "foldPostAssert RegSysSpec st 3" \<comment> \<open>folding of the post assertions directly preceding MRM\<close>

  from a1 have conjPost: "MRI_Reg_End st" \<comment> \<open>proving what the conjunction of the directly preceding post assertions are\<close>
    by (simp add: Reg_simps RegSysSpec_simps foldPostAssert_def mkSysSpec_def)

  from conjPost show "RegMRMPre (the (systemTasks st 3)) (systemChs st)"
    by (simp add: RegSysSpec_simps RegMRMPre_def)
qed

text \<open>MHS Precondition VC:
        MRM_End /\ True -> MHS Precondition\<close>

lemma RegMHSPre_sat: "taskPreSysVC RegSystem RegSysSpec RegTaskContracts st TID_MHS"
  unfolding taskPreSysVC_def
proof (auto simp add: RegTaskContracts_def TID_MRM_def RegTaskPreMap_def TID_Admin_def TID_MRI_def TID_MHS_def)
  assume a1: "foldPostAssert RegSysSpec st 4" \<comment> \<open>folding of the post assertions directly preceding MHS\<close>

  from a1 have conjPost: "MRM_Reg_End st" \<comment> \<open>proving what the conjunction of the directly preceding post assertions are\<close>
    by (simp add: Reg_simps RegSysSpec_simps foldPostAssert_def mkSysSpec_def)

  from conjPost show "RegMHSPre (the (systemTasks st 4)) (systemChs st)"
    by (simp add: RegSysSpec_simps RegMHSPre_def)
qed

text \<open>Complete precondition VC\<close>

lemma preVC:
  assumes tidInSys: "tid \<in> set (schedule RegSystem)"
  shows "taskPreVC RegSystem RegModel RegScheduleContract RegTaskContracts RegSysSpec tid"
  unfolding taskPreVC_def
  apply clarify
proof \<comment> \<open>Prove tasks that can appear at the start of the ordering satisfy startPreVC\<close>
  fix st
  show "wf_SystemState RegModel RegSystem st \<Longrightarrow>
        mayFollow RegScheduleContract (currTidSystemState st) tid \<Longrightarrow>
        tid \<in> getAllPoints (taskOrder RegSysSpec) \<Longrightarrow> 
        tid \<in> getStartPoints (taskOrder RegSysSpec) \<longrightarrow> startPreVC RegSystem RegSysSpec RegTaskContracts st tid \<and> funPreVC RegSystem RegSysSpec st"
  proof
    assume wf_st: "wf_SystemState RegModel RegSystem st" \<comment> \<open>st is a well formed state\<close>
    assume mf: "mayFollow RegScheduleContract (currTidSystemState st) tid" \<comment> \<open>tid may follow the current TID of st\<close>
    assume startPoint: "tid \<in> getStartPoints (taskOrder RegSysSpec)" \<comment> \<open>tid can appear at the start of the ordering defined in RegSysSpec\<close>
    from startPoint have tidPossible: "tid \<in> {TID_Admin}" \<comment> \<open>State all points that can appear at the start\<close>
      by (auto simp add: getStartPoints_def RegSysSpec_simps mkSysSpec_def)
    from tidPossible show "startPreVC RegSystem RegSysSpec RegTaskContracts st tid \<and> funPreVC RegSystem RegSysSpec st"
      using DisplayTempPreVC RegAdminPre_sat by auto
  qed
next \<comment> \<open>Prove tasks that don't appear at the start of the ordering satisfy taskPreSysVC\<close>
  fix st
  show "wf_SystemState RegModel RegSystem st \<Longrightarrow>
        mayFollow RegScheduleContract (currTidSystemState st) tid \<Longrightarrow>
        tid \<in> getAllPoints (taskOrder RegSysSpec) \<Longrightarrow> 
        tid \<notin> getStartPoints (taskOrder RegSysSpec) \<longrightarrow> taskPreSysVC RegSystem RegSysSpec RegTaskContracts st tid"
  proof
    assume wf_st: "wf_SystemState RegModel RegSystem st" \<comment> \<open>st is a well formed state\<close>
    assume mf: "mayFollow RegScheduleContract (currTidSystemState st) tid" \<comment> \<open>tid may follow the current TID of st\<close>
    assume tid1: "tid \<in> getAllPoints (taskOrder RegSysSpec)" \<comment> \<open>tid must appear in the ordering\<close>
    assume tid2: "tid \<notin> getStartPoints (taskOrder RegSysSpec)" \<comment> \<open>tid is not a start point of the ordering\<close>
    from tid1 tid2 have tidPossible: "tid \<in> {TID_MRI, TID_MRM, TID_MHS}" \<comment> \<open>State all points that don't appear at the start\<close>
      by (auto simp add: getStartPoints_def getAllPoints_def RegSysSpec_simps mkSysSpec_def)
    from tidPossible show "taskPreSysVC RegSystem RegSysSpec RegTaskContracts st tid"
      by (auto simp add: RegMRIPre_sat RegMRMPre_sat RegMHSPre_sat)
  qed
qed

(* ---------------- Post ---------------- *)

(*
  Post VCs are a lot more inconsistent in how they are proven, patterns are starting to arise
  though with establishing facts that represent the frame conditions and updates using

    by (smt (z3) act char.inject fun_upd_other fun_upd_same list.inject option.sel)

  which solves most action related properties. Conditionals are a lot more inconsistent in their 
  proofs, especially when they are nested, as they require a conditional update to be stated for 
  all paths and then proven with linear arithmetic. There is still a significant amount
  work that needs to be done to clean up the proofs

  Proving said VCs over a step is very consistent with it being done exactly the same between the
  two examples
*)

text \<open>Admin_End VC:
        Admin_End is satisfied for st2 if the display temp precondition is true for st1\<close>

lemma Admin_End_sat: "\<lbrakk>DisplayTempRegPre st1; do_action ((systemTasks st1) $ TID_Admin, systemChs st1) A_Admin = ((systemTasks st2) $ TID_Admin, systemChs st2)\<rbrakk> \<Longrightarrow> Admin_Reg_End st2"
proof (auto simp add: A_Admin_def Admin_Reg_End_def RegSysSpec_def mkSysSpec_def DisplayTempRegPre_def) \<comment> \<open>''lower_desired_tempWstatus_ad'' < ''upper_desired_tempWstatus_ad'' after reading the external ports\<close>
  assume pre: "the (systemChs st1 ''lower_desired_tempWstatus'') \<le> the (systemChs st1 ''upper_desired_tempWstatus'')" \<comment> \<open>Display temp function precondition\<close>
  assume act: "(systemChs st1)
    (''upper_desired_tempWstatus_ad'' \<mapsto> the (systemChs st1 ''upper_desired_tempWstatus''), ''lower_desired_tempWstatus_ad'' \<mapsto> the (systemChs st1 ''lower_desired_tempWstatus''),
       ''current_tempWstatus_ad'' \<mapsto> the (systemChs st1 ''current_tempWstatus''), ''regulator_mode_logged'' \<mapsto> the (systemChs st1 ''regulator_mode'')) =
    systemChs st2" \<comment> \<open>the action descried as a relationship between st1 and st2\<close>

  \<comment> \<open>facts that are slices of the update of the state as defined by the action\<close>
  have low_eq: "the (systemChs st1 ''lower_desired_tempWstatus'') = the (systemChs st2 ''lower_desired_tempWstatus_ad'')" \<comment> \<open>''lower_desired_tempWstatus'' is equal to ''lower_desired_tempWstatus_ad''\<close>
    by (smt (z3) act char.inject fun_upd_other fun_upd_same list.inject option.sel) 
  have high_eq: "the (systemChs st1 ''upper_desired_tempWstatus'') = the (systemChs st2 ''upper_desired_tempWstatus_ad'')" \<comment> \<open>''upper_desired_tempWstatus'' is equal to ''upper_desired_tempWstatus_ad''\<close>
    by (smt (z3) act char.inject fun_upd_other fun_upd_same list.inject option.sel) 

  show "the (systemChs st2 ''lower_desired_tempWstatus_ad'') \<le> the (systemChs st2 ''upper_desired_tempWstatus_ad'')"
    using high_eq low_eq pre by presburger
next \<comment> \<open>regulator mode is equal to the logged regulator mode value after reading in the value\<close>
  assume pre: "the (systemChs st1 ''lower_desired_tempWstatus'') \<le> the (systemChs st1 ''upper_desired_tempWstatus'')"
  assume act: "(systemChs st1)
    (''upper_desired_tempWstatus_ad'' \<mapsto> the (systemChs st1 ''upper_desired_tempWstatus''), ''lower_desired_tempWstatus_ad'' \<mapsto> the (systemChs st1 ''lower_desired_tempWstatus''),
       ''current_tempWstatus_ad'' \<mapsto> the (systemChs st1 ''current_tempWstatus''), ''regulator_mode_logged'' \<mapsto> the (systemChs st1 ''regulator_mode'')) =
    systemChs st2"

  show "the (systemChs st2 ''regulator_mode'') = the (systemChs st2 ''regulator_mode_logged'')"
    by (smt (z3) act fun_upd_other fun_upd_same list.distinct(1) list.inject option.sel)
qed

text \<open>Admin_End_sat holds over a system step\<close>

lemma RegAdminPost_satisfied_step:
  assumes wf_st: "wf_SystemState RegModel RegSystem st1"
      and step: "systemStep RegSystem st1 st2"
      and currTidTID1: "currTid (scheduleState st2) = TID_Admin"
    shows "startPostAssertVC RegSystem RegSysSpec RegTaskContracts TID_Admin st1 st2"
  unfolding startPostAssertVC_def
proof (simp add: RegSysSpec_def mkSysSpec_def Reg_End_def)
  obtain systemTasks1 systemChs1 taskState' tid tidAction tscs scheduleState2 systemTasks2 systemChs2 where
    p0: "systemTasks1 = systemTasks st1" and
    p1: "systemChs1 = systemChs st1" and
    p2: "scheduleState2 = scheduleNext (schedule RegSystem) (scheduleState st1)" and
    p2a: "tid = (currTid scheduleState2)" and
    p3: "tidAction = action ((taskMap RegSystem) $ tid)" and
    p4: "taskState' = systemTasks1 $ tid" and
    p5: "tscs = do_action (taskState', systemChs1) tidAction" and
    p5a: "systemTasks2 = systemTasks1 (tid \<mapsto> fst tscs)" and
    p5b: "systemChs2 = snd tscs" and
    p6: "st2 = mkSystemState systemTasks2 systemChs2 scheduleState2 systemTasks1 systemChs1"
    using step
    by (metis systemStep.simps)
  from currTidTID1 p2 p2a p6 have tidisTIDSquaring: "tid = TID_Admin"
    by (simp add: mkSystemState_def)
  from tidisTIDSquaring p3 have tidActionisASquaring: "tidAction = A_Admin" by (simp add: Reg_simps)
  from p0 p1 p4 p5 p5a p5b p6 tidisTIDSquaring tidActionisASquaring have AAdminExec: "do_action ((systemTasks st1) $ TID_Admin, systemChs st1) A_Admin = ((systemTasks st2) $ TID_Admin, systemChs st2)"
    by (simp add: mkSystemState_def)
  show "DisplayTempRegPre st1 \<longrightarrow> Admin_Reg_End st2"
  proof
    assume precond: "DisplayTempRegPre st1"
    from precond AAdminExec show "Admin_Reg_End st2"
      using Admin_End_sat by auto
  qed
qed

text \<open>MRI_End VC:
        MRI_End is satisfied for st2 if the all directly preceding post condition are true is true for st1\<close>

lemma MRI_End_sat: "\<lbrakk>foldPostAssert RegSysSpec st1 TID_MRI; 
                     do_action ((systemTasks st1) $ TID_MRI, systemChs st1) A_MRI = ((systemTasks st2) $ TID_MRI, systemChs st2)\<rbrakk> 
                     \<Longrightarrow> MRI_Reg_End st2"
  unfolding MRI_Reg_End_def
proof -
  assume foldedPost: "foldPostAssert RegSysSpec st1 TID_MRI" \<comment> \<open>folding of the post assertions directly preceding MRI\<close>
  assume act: "do_action (the (systemTasks st1 TID_MRI), systemChs st1) A_MRI = (the (systemTasks st2 TID_MRI), systemChs st2)" \<comment> \<open>action that is not fully expanded\<close>

  from foldedPost have conjPost: "Admin_Reg_End st1" \<comment> \<open>evaluating the fold to the resulting conjunction of the directly preceding post conditions\<close>
    by (simp add: Reg_simps RegSysSpec_simps foldPostAssert_def mkSysSpec_def)

  from act conjPost show "the (systemChs st2 ''lower_desired_temp'') \<le> the (systemChs st2 ''upper_desired_temp'') \<and>
                          Req_REG_DisplayTemp (the (systemChs st2 ''regulator_mode_logged'')) (the (systemChs st2 ''current_tempWstatus_ad'')) (the (systemChs st2 ''display_temp''))"
  proof (simp add: Admin_Reg_End_def A_MRI_def Req_REG_DisplayTemp_def Req_REG_DisplayTemp_1_def Req_REG_DisplayTemp_2_def)
    assume act: "the (systemTasks st1 TID_MRI) = the (systemTasks st2 TID_MRI) \<and>
    (systemChs st1)
    (''upper_desired_temp'' \<mapsto> the (systemChs st1 ''upper_desired_tempWstatus_ad''), ''lower_desired_temp'' \<mapsto> the (systemChs st1 ''lower_desired_tempWstatus_ad''),
       ''display_temp'' \<mapsto>
       if the (systemChs st1 ''regulator_mode_logged'') = 1 then the (snd (the (systemTasks st1 TID_MRI), systemChs st1) ''current_tempWstatus_ad'')
       else the (snd (the (systemTasks st1 TID_MRI), systemChs st1) ''display_temp'')) =
    systemChs st2" \<comment> \<open>Fully expanded action\<close>
    assume conjPost: "the (systemChs st1 ''lower_desired_tempWstatus_ad'') \<le> the (systemChs st1 ''upper_desired_tempWstatus_ad'') \<and>
                      the (systemChs st1 ''regulator_mode'') = the (systemChs st1 ''regulator_mode_logged'')"

    \<comment> \<open>frame conditions\<close>
    have frame1: "the (systemChs st1 ''current_tempWstatus_ad'') = the (systemChs st2 ''current_tempWstatus_ad'')"
      by (smt (z3) act char.inject fun_upd_other fun_upd_same list.inject option.sel)
    have frame2: "the (systemChs st1 ''regulator_mode_logged'') = the (systemChs st2 ''regulator_mode_logged'')"
      by (smt (z3) act char.inject fun_upd_other fun_upd_same list.inject option.sel)

    \<comment> \<open>update properties\<close>
    have low_eq: "the (systemChs st1 ''lower_desired_tempWstatus_ad'') = the (systemChs st2 ''lower_desired_temp'')"
      by (smt (z3) act char.inject fun_upd_other fun_upd_same list.inject option.sel)
    have up_eq: "the (systemChs st1 ''upper_desired_tempWstatus_ad'') = the (systemChs st2 ''upper_desired_temp'')"
      by (smt (z3) act char.inject fun_upd_other fun_upd_same list.inject option.sel) 

    \<comment> \<open>post 1\<close>
    from low_eq up_eq conjPost have post1: "the (systemChs st2 ''lower_desired_temp'') \<le> the (systemChs st2 ''upper_desired_temp'')"
      by presburger

    \<comment> \<open>post 3\<close>
    \<comment> \<open>post3_1: if update property\<close>
    have post3_1: "the (systemChs st2 ''display_temp'') = (if the (systemChs st1 ''regulator_mode_logged'') = 1 then the (snd (the (systemTasks st1 TID_MRI), systemChs st1) ''current_tempWstatus_ad'') else the (snd (the (systemTasks st1 TID_MRI), systemChs st1) ''display_temp''))"
      by (smt (verit, best) act fun_upd_same option.sel)
    \<comment> \<open>post3_2: rewrite of the if branch as an implication\<close>
    from post3_1 have post3_2: "the (systemChs st1 ''regulator_mode_logged'') = 1 \<longrightarrow> the (systemChs st2 ''display_temp'') = the (systemChs st1 ''current_tempWstatus_ad'')"
      by auto
    \<comment> \<open>post3: replace ''current_tempWstatus_ad'' with ''current_tempWstatus_MRI''\<close>
    from post3_2 frame1 frame2 have post3: "(the (systemChs st2 ''regulator_mode_logged'') = 1 \<longrightarrow> the (systemChs st2 ''display_temp'') = the (systemChs st2 ''current_tempWstatus_ad''))"
      by presburger

    show "the (systemChs st2 ''lower_desired_temp'') \<le> the (systemChs st2 ''upper_desired_temp'') \<and>
          (the (systemChs st2 ''regulator_mode_logged'') = 1 \<longrightarrow> the (systemChs st2 ''display_temp'') = the (systemChs st2 ''current_tempWstatus_ad''))"
      by (auto simp add: post1 post3)
  qed
qed

text \<open>MRI_End_sat holds over a system step\<close>

lemma RegMRIPost_satisfied_step:
  assumes wf_st: "wf_SystemState RegModel RegSystem st1"
      and step: "systemStep RegSystem st1 st2"
      and currTidTID1: "currTid (scheduleState st2) = TID_MRI"
    shows "taskPostAssertVC RegSystem RegSysSpec RegTaskContracts TID_MRI st1 st2"
  unfolding taskPostAssertVC_def
proof -
  obtain systemTasks1 systemChs1 taskState' tid tidAction tscs scheduleState2 systemTasks2 systemChs2 where
    p0: "systemTasks1 = systemTasks st1" and
    p1: "systemChs1 = systemChs st1" and
    p2: "scheduleState2 = scheduleNext (schedule RegSystem) (scheduleState st1)" and
    p2a: "tid = (currTid scheduleState2)" and
    p3: "tidAction = action ((taskMap RegSystem) $ tid)" and
    p4: "taskState' = systemTasks1 $ tid" and
    p5: "tscs = do_action (taskState', systemChs1) tidAction" and
    p5a: "systemTasks2 = systemTasks1 (tid \<mapsto> fst tscs)" and
    p5b: "systemChs2 = snd tscs" and
    p6: "st2 = mkSystemState systemTasks2 systemChs2 scheduleState2 systemTasks1 systemChs1"
    using step
    by (metis systemStep.simps)
  from currTidTID1 p2 p2a p6 have tidisTIDSquaring: "tid = TID_MRI"
    by (simp add: mkSystemState_def)
  from tidisTIDSquaring p3 have tidActionisASquaring: "tidAction = A_MRI" by (simp add: Reg_simps)
  from p0 p1 p4 p5 p5a p5b p6 tidisTIDSquaring tidActionisASquaring have AMRIExec: "do_action ((systemTasks st1) $ TID_MRI, systemChs st1) A_MRI = ((systemTasks st2) $ TID_MRI, systemChs st2)"
    by (simp add: mkSystemState_def)
  show "foldPostAssert RegSysSpec st1 TID_MRI \<longrightarrow> the (sysTasksAsserts RegSysSpec TID_MRI) st2"
  proof
    assume precond: "foldPostAssert RegSysSpec st1 TID_MRI"
    from precond AMRIExec have "MRI_Reg_End st2"
      using MRI_End_sat by auto 
    thus "the (sysTasksAsserts RegSysSpec TID_MRI) st2" by (auto simp add: Reg_simps RegSysSpec_simps mkSysSpec_def)
  qed
qed

text \<open>MRM_End VC:
        MRM_End is satisfied for st2 if the all directly preceding post condition are true is true for st1\<close>

lemma MRM_End_sat: "\<lbrakk>foldPostAssert RegSysSpec st1 TID_MRM; 
                     do_action ((systemTasks st1) $ TID_MRM, systemChs st1) A_MRM = ((systemTasks st2) $ TID_MRM, systemChs st2)\<rbrakk> 
                     \<Longrightarrow> MRM_Reg_End st2"
  unfolding MRM_Reg_End_def
proof -
  assume foldPost: "foldPostAssert RegSysSpec st1 TID_MRM" \<comment> \<open>folding of the post assertions directly MRM\<close>
  assume act: "do_action (the (systemTasks st1 TID_MRM), systemChs st1) A_MRM = (the (systemTasks st2 TID_MRM), systemChs st2)" \<comment> \<open>action that is not fully expanded\<close>

  from foldPost have conjPost: "MRI_Reg_End st1" \<comment> \<open>evaluating the fold to the resulting conjunction of the directly preceding post conditions\<close>
    by (simp add: Reg_simps RegSysSpec_simps foldPostAssert_def mkSysSpec_def)

  from act conjPost show "Req_REG_DisplayTemp (the (systemChs st2 ''regulator_mode_logged'')) (the (systemChs st2 ''current_tempWstatus_ad'')) (the (systemChs st2 ''display_temp'')) \<and> 
                          the (systemChs st2 ''lower_desired_temp'') \<le> the (systemChs st2 ''upper_desired_temp'')"
  proof (simp add: MRI_Reg_End_def A_MRM_def Req_REG_DisplayTemp_def Req_REG_DisplayTemp_1_def Req_REG_DisplayTemp_2_def)
    assume act: "the (systemTasks st1 TID_MRM) = the (systemTasks st2 TID_MRM) \<and> (systemChs st1)(''regulator_mode'' \<mapsto> 1) = systemChs st2" \<comment> \<open>Fully expanded action\<close>
    assume conjPost: "the (systemChs st1 ''lower_desired_temp'') \<le> the (systemChs st1 ''upper_desired_temp'') \<and>
    (the (systemChs st1 ''regulator_mode_logged'') = 1 \<longrightarrow> the (systemChs st1 ''display_temp'') = the (systemChs st1 ''current_tempWstatus_ad''))" \<comment> \<open>fully expanded conjunction of the directly preceding post assertion\<close>

    \<comment> \<open>Frame conditions\<close>
    have frame1: "the (systemChs st1 ''regulator_mode_logged'') = the (systemChs st2 ''regulator_mode_logged'')"
      by (smt (z3) act fun_upd_other fun_upd_same list.distinct(1) list.inject option.sel)
    have frame2: "the (systemChs st1 ''display_temp'') = the (systemChs st2 ''display_temp'')"
      by (smt (z3) act fun_upd_other fun_upd_same list.distinct(1) list.inject option.sel)
    have frame3: "the (systemChs st1 ''current_tempWstatus_ad'') = the (systemChs st2 ''current_tempWstatus_ad'')"
      by (smt (z3) act fun_upd_other fun_upd_same list.distinct(1) list.inject option.sel)
    have frame4: "the (systemChs st1 ''lower_desired_temp'') = the (systemChs st2 ''lower_desired_temp'')"
      by (smt (z3) act fun_upd_other fun_upd_same list.distinct(1) list.inject option.sel)
    have frame5: "the (systemChs st1 ''upper_desired_temp'') = the (systemChs st2 ''upper_desired_temp'')"
      by (smt (z3) act fun_upd_other fun_upd_same list.distinct(1) list.inject option.sel)


    show "(the (systemChs st2 ''regulator_mode_logged'') = 1 \<longrightarrow> the (systemChs st2 ''display_temp'') = the (systemChs st2 ''current_tempWstatus_ad'')) 
          \<and> the (systemChs st2 ''lower_desired_temp'') \<le> the (systemChs st2 ''upper_desired_temp'')"
      using conjPost frame1 frame2 frame3 frame4 frame5 by presburger
  qed
qed

text \<open>MRM_End_sat holds over a system step\<close>

lemma RegMRMPost_satisfied_step:
  assumes wf_st: "wf_SystemState RegModel RegSystem st1"
      and step: "systemStep RegSystem st1 st2"
      and currTidTID1: "currTid (scheduleState st2) = TID_MRM"
    shows "taskPostAssertVC RegSystem RegSysSpec RegTaskContracts TID_MRM st1 st2"
  unfolding taskPostAssertVC_def
proof -
  obtain systemTasks1 systemChs1 taskState' tid tidAction tscs scheduleState2 systemTasks2 systemChs2 where
    p0: "systemTasks1 = systemTasks st1" and
    p1: "systemChs1 = systemChs st1" and
    p2: "scheduleState2 = scheduleNext (schedule RegSystem) (scheduleState st1)" and
    p2a: "tid = (currTid scheduleState2)" and
    p3: "tidAction = action ((taskMap RegSystem) $ tid)" and
    p4: "taskState' = systemTasks1 $ tid" and
    p5: "tscs = do_action (taskState', systemChs1) tidAction" and
    p5a: "systemTasks2 = systemTasks1 (tid \<mapsto> fst tscs)" and
    p5b: "systemChs2 = snd tscs" and
    p6: "st2 = mkSystemState systemTasks2 systemChs2 scheduleState2 systemTasks1 systemChs1"
    using step
    by (metis systemStep.simps)
  from currTidTID1 p2 p2a p6 have tidisTIDSquaring: "tid = TID_MRM"
    by (simp add: mkSystemState_def)
  from tidisTIDSquaring p3 have tidActionisASquaring: "tidAction = A_MRM" by (simp add: Reg_simps)
  from p0 p1 p4 p5 p5a p5b p6 tidisTIDSquaring tidActionisASquaring have AMRMExec: "do_action ((systemTasks st1) $ TID_MRM, systemChs st1) A_MRM = ((systemTasks st2) $ TID_MRM, systemChs st2)"
    by (simp add: mkSystemState_def)
  show "foldPostAssert RegSysSpec st1 TID_MRM \<longrightarrow> the (sysTasksAsserts RegSysSpec TID_MRM) st2"
  proof
    assume precond: "foldPostAssert RegSysSpec st1 TID_MRM"
    from precond AMRMExec have "MRM_Reg_End st2"
      using MRM_End_sat by auto 
    thus "the (sysTasksAsserts RegSysSpec TID_MRM) st2" by (auto simp add: Reg_simps RegSysSpec_simps mkSysSpec_def)
  qed
qed    

text \<open>MHS_End VC:
        MHS_End is satisfied for st2 if the all directly preceding post condition are true is true for st1\<close>

(* Think about modifies: 
    . Give frame conditions
    . Predicate to describe the action*)

lemma MHS_End_sat: "\<lbrakk>foldPostAssert RegSysSpec st1 TID_MHS; 
                     do_action ((systemTasks st1) $ TID_MHS, systemChs st1) A_MHS = ((systemTasks st2) $ TID_MHS, systemChs st2)\<rbrakk> 
                     \<Longrightarrow> MHS_Reg_End st2"
  unfolding MHS_Reg_End_def
proof -    
  assume foldedPost: "foldPostAssert RegSysSpec st1 TID_MHS" \<comment> \<open>folding of the post assertions directly MHS\<close>
  assume act: "do_action (the (systemTasks st1 TID_MHS), systemChs st1) A_MHS = (the (systemTasks st2 TID_MHS), systemChs st2)" \<comment> \<open>action that is not fully expanded\<close>

  from foldedPost have conjPost: "MRM_Reg_End st1"  \<comment> \<open>evaluating the fold to the resulting conjunction of the directly preceding post conditions\<close>
    by (simp add: Reg_simps RegSysSpec_simps foldPostAssert_def mkSysSpec_def)

  from act conjPost show " Req_REG_DisplayTemp (the (systemChs st2 ''regulator_mode_logged'')) (the (systemChs st2 ''current_tempWstatus_ad'')) (the (systemChs st2 ''display_temp''))"
  proof (simp add: MRM_Reg_End_def A_MHS_def Req_REG_DisplayTemp_def Req_REG_DisplayTemp_1_def Req_REG_DisplayTemp_2_def)
    assume act: "(if the (systemChs st1 ''regulator_mode'') = 1
     then if the (snd (the (systemTasks st1 TID_MHS), systemChs st1) ''current_tempWstatus_ad'') < the (snd (the (systemTasks st1 TID_MHS), systemChs st1) ''lower_desired_temp'')
          then (fst (the (systemTasks st1 TID_MHS), systemChs st1), snd (the (systemTasks st1 TID_MHS), systemChs st1) ++ [''heat_control'' \<mapsto> 1])
          else if the (snd (the (systemTasks st1 TID_MHS), systemChs st1) ''upper_desired_temp'') < the (snd (the (systemTasks st1 TID_MHS), systemChs st1) ''current_tempWstatus_ad'')
               then (fst (the (systemTasks st1 TID_MHS), systemChs st1), snd (the (systemTasks st1 TID_MHS), systemChs st1) ++ [''heat_control'' \<mapsto> 0]) 
               else (the (systemTasks st1 TID_MHS), systemChs st1)
     else (fst (the (systemTasks st1 TID_MHS), systemChs st1), snd (the (systemTasks st1 TID_MHS), systemChs st1) ++ [''heat_control'' \<mapsto> 0])) =
    (the (systemTasks st2 TID_MHS), systemChs st2)" \<comment> \<open>Fully expanded action\<close>

    \<comment> \<open>Update properties for if statements\<close>
    have branch1: "the (systemChs st1 ''regulator_mode'') \<noteq> 1 \<longrightarrow> systemChs st2 = (systemChs st1) ++ [''heat_control'' \<mapsto> 0]"
      using act by fastforce
    have branch2: "the (systemChs st1 ''regulator_mode'') = 1 \<longrightarrow> the (snd (the (systemTasks st1 TID_MHS), systemChs st1) ''current_tempWstatus_ad'') < the (snd (the (systemTasks st1 TID_MHS), systemChs st1) ''lower_desired_temp'') \<longrightarrow> systemChs st2 = (systemChs st1) ++ [''heat_control'' \<mapsto> 1]"
      using act by fastforce
    have branch3: "the (systemChs st1 ''regulator_mode'') = 1 \<longrightarrow> the (snd (the (systemTasks st1 TID_MHS), systemChs st1) ''current_tempWstatus_ad'') \<ge> the (snd (the (systemTasks st1 TID_MHS), systemChs st1) ''lower_desired_temp'') 
          \<longrightarrow> the (snd (the (systemTasks st1 TID_MHS), systemChs st1) ''upper_desired_temp'') < the (snd (the (systemTasks st1 TID_MHS), systemChs st1) ''current_tempWstatus_ad'') \<longrightarrow> systemChs st2 = (systemChs st1) ++ [''heat_control'' \<mapsto> 0]"
      using act by fastforce
    have branch4: "the (systemChs st1 ''regulator_mode'') = 1 \<longrightarrow> the (snd (the (systemTasks st1 TID_MHS), systemChs st1) ''current_tempWstatus_ad'') \<ge> the (snd (the (systemTasks st1 TID_MHS), systemChs st1) ''lower_desired_temp'') 
          \<longrightarrow> the (snd (the (systemTasks st1 TID_MHS), systemChs st1) ''upper_desired_temp'') \<ge> the (snd (the (systemTasks st1 TID_MHS), systemChs st1) ''current_tempWstatus_ad'') \<longrightarrow> systemChs st2 = (systemChs st1)"
      using act by fastforce

    \<comment> \<open>All possible updates to the Channel state\<close>
    have allUpdate: "systemChs st2 = (systemChs st1) ++ [''heat_control'' \<mapsto> 1] \<or> systemChs st2 = (systemChs st1) ++ [''heat_control'' \<mapsto> 0] \<or> systemChs st2 = (systemChs st1)"
      using branch1 branch2 branch3 branch4 by linarith

    \<comment> \<open>Frame conditions\<close>
    from act allUpdate have frame1: "the (systemChs st1 ''display_temp'') = the (systemChs st2 ''display_temp'')"
      by auto
    from act allUpdate have frame2: "the (systemChs st1 ''current_tempWstatus_ad'') = the (systemChs st2 ''current_tempWstatus_ad'')"
      by auto
    from act allUpdate have frame3: "the (systemChs st1 ''regulator_mode_logged'') = the (systemChs st2 ''regulator_mode_logged'')"
      by auto

    show "the (systemChs st2 ''regulator_mode_logged'') = 1 \<longrightarrow> the (systemChs st2 ''display_temp'') = the (systemChs st2 ''current_tempWstatus_ad'')"
      using conjPost frame1 frame2 frame3
      by (simp add: MRM_Reg_End_def Req_REG_DisplayTemp_1_def Req_REG_DisplayTemp_def) 
  qed
qed

text \<open>MHS_End_sat holds over a system step\<close>

lemma RegMHSPost_satisfied_step:
  assumes wf_st: "wf_SystemState RegModel RegSystem st1"
      and step: "systemStep RegSystem st1 st2"
      and currTidTID1: "currTid (scheduleState st2) = TID_MHS"
    shows "taskPostAssertVC RegSystem RegSysSpec RegTaskContracts TID_MHS st1 st2"
  unfolding taskPostAssertVC_def
proof -
  obtain systemTasks1 systemChs1 taskState' tid tidAction tscs scheduleState2 systemTasks2 systemChs2 where
    p0: "systemTasks1 = systemTasks st1" and
    p1: "systemChs1 = systemChs st1" and
    p2: "scheduleState2 = scheduleNext (schedule RegSystem) (scheduleState st1)" and
    p2a: "tid = (currTid scheduleState2)" and
    p3: "tidAction = action ((taskMap RegSystem) $ tid)" and
    p4: "taskState' = systemTasks1 $ tid" and
    p5: "tscs = do_action (taskState', systemChs1) tidAction" and
    p5a: "systemTasks2 = systemTasks1 (tid \<mapsto> fst tscs)" and
    p5b: "systemChs2 = snd tscs" and
    p6: "st2 = mkSystemState systemTasks2 systemChs2 scheduleState2 systemTasks1 systemChs1"
    using step
    by (metis systemStep.simps)
  from currTidTID1 p2 p2a p6 have tidisTIDSquaring: "tid = TID_MHS"
    by (simp add: mkSystemState_def)
  from tidisTIDSquaring p3 have tidActionisASquaring: "tidAction = A_MHS" by (simp add: Reg_simps)
  from p0 p1 p4 p5 p5a p5b p6 tidisTIDSquaring tidActionisASquaring have AMRMExec: "do_action ((systemTasks st1) $ TID_MHS, systemChs st1) A_MHS = ((systemTasks st2) $ TID_MHS, systemChs st2)"
    by (simp add: mkSystemState_def)
  show "foldPostAssert RegSysSpec st1 TID_MHS \<longrightarrow> the (sysTasksAsserts RegSysSpec TID_MHS) st2"
  proof
    assume precond: "foldPostAssert RegSysSpec st1 TID_MHS"
    from precond AMRMExec have "MHS_Reg_End st2"
      using MHS_End_sat by auto 
    thus "the (sysTasksAsserts RegSysSpec TID_MHS) st2" by (auto simp add: Reg_simps RegSysSpec_simps mkSysSpec_def)
  qed
qed    

text \<open>Complete post-condition VC\<close>

lemma postVC: 
  assumes tidInSys: "tid \<in> systemTids RegSystem"
  shows "taskPostVC RegSystem RegModel RegTaskContracts RegSysSpec tid"
  unfolding taskPostVC_def
  apply clarify
proof \<comment> \<open>Prove tasks that can appear at the start of the ordering satisfy startPostAssertVC\<close>
  fix st1 st2
  assume wf_st: "wf_SystemState RegModel RegSystem st1" \<comment> \<open>st1 is well formed\<close>
  assume step: "systemStep RegSystem st1 st2" \<comment> \<open>can step from st1 to st2 in RegSystem\<close>
  assume inFlow: "currTidSystemState st2 \<in> getAllPoints (taskOrder RegSysSpec)" \<comment> \<open>st2 is in allPoints\<close>
  assume currTid: "tid = currTidSystemState st2" \<comment> \<open>tid is equal to the current TID of st2\<close>
  from tidInSys have tidset: "tid \<in> {TID_Admin, TID_MRI, TID_MRM, TID_MHS}" \<comment> \<open>all tids that in the task ordering\<close>
    by (simp add: Reg_simps)

  show "currTidSystemState st2 \<in> getStartPoints (taskOrder RegSysSpec) \<longrightarrow> startPostAssertVC RegSystem RegSysSpec RegTaskContracts (currTidSystemState st2) st1 st2"
    using "tidset" currTid
    apply auto
       apply (simp add: RegAdminPost_satisfied_step local.step wf_st) \<comment> \<open>RegAdminPost_satisfied\<close>
    by (auto simp add: RegSysSpec_def mkSysSpec_def getStartPoints_def RegSubSystemTaskOrdering_def) \<comment> \<open>show all other points are not in start points\<close>
next \<comment> \<open>Prove tasks that don't appear at the start of the ordering satisfy taskPostAssertVC\<close>
  fix st1 st2
  assume wf_st: "wf_SystemState RegModel RegSystem st1" \<comment> \<open>st1 is well formed\<close>
  assume step: "systemStep RegSystem st1 st2" \<comment> \<open>can step from st1 to st2 in RegSystem\<close>
  assume inFlow: "currTidSystemState st2 \<in> getAllPoints (taskOrder RegSysSpec)" \<comment> \<open>st2 is in allPoints\<close>
  assume currTid: "tid = currTidSystemState st2" \<comment> \<open>tid is equal to the current TID of st2\<close>
  from tidInSys have tidset: "tid \<in> {TID_Admin, TID_MRI, TID_MRM, TID_MHS}" \<comment> \<open>all tids that in the task ordering\<close>
    by (simp add: Reg_simps)

  show "currTidSystemState st2 \<notin> getStartPoints (taskOrder RegSysSpec) \<longrightarrow> taskPostAssertVC RegSystem RegSysSpec RegTaskContracts (currTidSystemState st2) st1 st2"
    using tidset currTid
    apply auto
       prefer 2
       apply (simp add: RegMRIPost_satisfied_step local.step wf_st) \<comment> \<open>RegMRIPost_satisfied\<close>
      prefer 2
      apply (simp add: RegMRMPost_satisfied_step local.step wf_st) \<comment> \<open>RegMRMPost_satisfied\<close>
     prefer 2
     apply (simp add: RegMHSPost_satisfied_step local.step wf_st) \<comment> \<open>RegMHSPost_satisfied\<close>
    by (auto simp add: RegSysSpec_def mkSysSpec_def getStartPoints_def RegSubSystemTaskOrdering_def TID_Admin_def TID_MRI_def TID_MRM_def TID_MHS_def) \<comment> \<open>All other points are in start points\<close>
qed

(* ---------------- Fun Post ------------------ *)

text \<open>Display Temp Function Post-condition VC:
        MHS_End /\ True -> Display Temp Function Post-condition\<close>

lemma DisplayTempPostVC: "funPostVC RegSystem RegModel RegSysSpec"
proof (auto simp add: funPostVC_def)
  fix st
  assume wf_st: "wf_SystemState RegModel RegSystem st" \<comment> \<open>st is well formed\<close>
  assume currTidInendPoints: "currTid (scheduleState st) \<in> getEndPoints (taskOrder RegSysSpec)" \<comment> \<open>the current TID of st is in the end points of the ordering defined in RegSysSpec\<close>
  assume foldPost: "foldFinalPostAssert RegSysSpec st" \<comment> \<open>fold all final post assertions\<close>
                                                                                                                                                              
  have c1: "{the (Reg_End t) st |t. (\<exists>a. a = Suc 0 \<and> t = 2 \<or> a = 2 \<and> t = 3 \<or> a = 3 \<and> t = 4) \<and> (\<forall>b. (t = Suc 0 \<longrightarrow> b \<noteq> 2) \<and> (t = 2 \<longrightarrow> b \<noteq> 3) \<and> (t = 3 \<longrightarrow> b \<noteq> 4))} =
        {the (Reg_End t) st |t. t = 4}" \<comment> \<open>collapse the set to all end points\<close>
    by fastforce

  from foldPost have "MHS_Reg_End st" \<comment> \<open>the conjunction of all final post asserts in the ordering\<close>
    apply (auto simp add: foldFinalPostAssert_def RegSysSpec_def mkSysSpec_def getEndPoints_def RegSubSystemTaskOrdering_def) 
    apply (auto simp add: TID_Admin_def TID_MRI_def TID_MRM_def TID_MHS_def c1)
    by (auto simp add: Reg_End_def TID_Admin_def TID_MRI_def TID_MRM_def TID_MHS_def)

  thus "funPost RegSysSpec st"
    by (auto simp add: RegSysSpec_def mkSysSpec_def MHS_Reg_End_def DisplayTempRegPost_def)
qed

(*---------------- ContractConformanceVCs  ---------------- *)

lemma ContractConformance: "ContractConformanceVCs RegSystem RegModel RegTaskContracts RegSysSpec RegScheduleContract"
  apply (simp add: ContractConformanceVCs_def)
  by (metis RegScheduleContracts_wf RegSubSysSpec_wf RegTaskContracts_wf Reg_ScheduleContractsVC 
            DisplayTempPostVC nextTidInSys postVC preVC stepNextTidCurrTid subset_iff taskPostVC_def wf_RegModel 
            wf_RegSystem wf_SystemSpec_def wf_SystemSpec_domWRTControlFlow_def wf_SystemSpec_domWRTSchedule_def)

end