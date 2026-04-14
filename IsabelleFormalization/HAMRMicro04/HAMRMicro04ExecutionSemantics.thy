theory HAMRMicro04ExecutionSemantics
  imports HAMRMicro04Model
begin

section \<open>Definitions for Execution (Semantics)\<close>

subsection \<open>Single Step Execution\<close>

text \<open>Define a helper function to abstract the execution of the behavior of each
task.  This function just "runs" the action on the given store.\<close>

fun do_action :: " ('value TaskState \<times> 'value ChState) 
                 \<Rightarrow> 'value Action
                 \<Rightarrow> ('value TaskState \<times> 'value ChState)"

  where "do_action tscs a = (a tscs)"

text \<open>Jacob: we might consider refactoring or adding some helper methods to improve
      the readability of definition below.  Especially the equality with sysState'.
      Another possibility might be to use pattern matching on the tscs' pair to 
      directly name the subcomponents instead of having to use fst and snd but
      I don't know if this causes hiccups in the inductive proof tactic if the elements on
      the left side of the equality below are not variables at the top level.\<close>

inductive systemStep for sys::"'value System"
                where
 step: "\<lbrakk>scheduleState' = scheduleNext (schedule sys) (scheduleState sysState) ;
         tidAction = action ((taskMap sys) $ (currTid scheduleState'));
         tscs' = do_action ((systemTasks sysState) $ (currTid scheduleState'), (systemChs sysState)) tidAction;
         sysState' = mkSystemState ((systemTasks sysState) ((currTid scheduleState') \<mapsto> (fst tscs'))) 
                                   (snd tscs') scheduleState' (systemTasks sysState) (systemChs sysState)\<rbrakk>
  \<Longrightarrow> systemStep sys sysState sysState'"

text \<open>Next we prove some properties that establish the relationships between
the current store and previous store after performing a system step.\<close>

text \<open>First we prove that the store in the "history" of st2 is the store
from st1.\<close>

lemma stepCurrentStorePreviousStore:
  assumes step: "systemStep sys st1 st2"
  shows "systemTasks st1 = previousSystemTasks st2 \<and> systemChs st1 = previousSystemChs st2"
proof -
  obtain systemTasks1 systemChs1 taskState' tid tidAction tscs scheduleState2 systemTasks2 systemChs2 where
    p0: "systemTasks1 = systemTasks st1" and
    p1: "systemChs1 = systemChs st1" and
    p2: "scheduleState2 = scheduleNext (schedule sys) (scheduleState st1)" and
    p2a: "tid = (currTid scheduleState2)" and
    p3: "tidAction = action ((taskMap sys) $ tid)" and
    p4: "taskState' = systemTasks1 $ tid" and
    p5: "tscs = do_action (taskState', systemChs1) tidAction" and
    p5a: "systemTasks2 = systemTasks1 (tid \<mapsto> fst tscs)" and
    p5b: "systemChs2 = snd tscs" and
    p6: "st2 = mkSystemState systemTasks2 systemChs2 scheduleState2 systemTasks1 systemChs1"
    using step
    by (metis systemStep.simps)
  from p0 p1 p6 show ?thesis by (auto simp add: mkSystemState_def)
qed

text \<open>A similar property shows the relationship between the nextTid in a state
and the currTid in its successor.\<close>

lemma stepNextTidCurrTid:
  assumes step: "systemStep sys st1 st2"
  shows "nextTidSystemState sys st1 = currTidSystemState st2"
proof -
  obtain systemTasks1 systemChs1 taskState' tid tidAction tscs scheduleState2 systemTasks2 systemChs2 where
    p0: "systemTasks1 = systemTasks st1" and
    p1: "systemChs1 = systemChs st1" and
    p2: "scheduleState2 = scheduleNext (schedule sys) (scheduleState st1)" and
    p2a: "tid = (currTid scheduleState2)" and
    p3: "tidAction = action ((taskMap sys) $ tid)" and
    p4: "taskState' = systemTasks1 $ tid" and
    p5: "tscs = do_action (taskState', systemChs1) tidAction" and
    p5a: "systemTasks2 = systemTasks1 (tid \<mapsto> fst tscs)" and
    p5b: "systemChs2 = snd tscs" and
    p6: "st2 = mkSystemState systemTasks2 systemChs2 scheduleState2 systemTasks1 systemChs1"
    using step
    by (metis systemStep.simps)
  from p2 p6 show ?thesis by (auto simp add: mkSystemState_def)
qed

subsection \<open>Multi-Step and System Execution\<close>

definition systemReach :: "'store System \<Rightarrow> 'store SystemState \<Rightarrow> bool" where 
 "systemReach sys st = ((systemStep sys)\<^sup>*\<^sup>* (initSystemState sys) st)"

subsection \<open>Proof Support\<close>

subsubsection \<open>Execution of Well-formed Models Yields Well-formed States\<close>

text \<open>Given a well-formed system, the initial execution state is well-formed.\<close>

(*
lemma initial_state_wellformed: 
  assumes wf_model: "wf_Model m"
      and wf_sys: "wf_System sys m"
    shows "wf_SystemState m sys (initSystemState sys)" using wf_sys
  by (auto simp add: wf_System_simps wf_SystemState_simps wf_Model_simps wf_TaskState_def wf_VarState_dom_def)
*)

lemma currTidInSysORinitTid:
  assumes wf_model: "wf_Model m"
      and wf_sys: "wf_System sys m"
      and wf_st: "wf_SystemState m sys st"
    shows "currTidSystemState st \<in> systemTids sys \<union> {initTid}"
  using assms by (simp add: wf_System_Schedule_def wf_SystemState_simps wf_ScheduleState_simps)

text \<open>The next Tid to be scheduled is always in the systemTids (not the initTid).\<close>

lemma nextTidInSys:
  assumes wf_model: "wf_Model m"
      and wf_sys: "wf_System sys m"
      and wf_st: "wf_SystemState m sys st"
    shows "nextTidSystemState sys st \<in> systemTids sys"
proof -
  let ?a = "scheduleNext (schedule sys) (scheduleState st)"
  from assms have "wf_ScheduleState_currTid_inSys sys (currTid ?a)" 
    unfolding wf_SystemState_def using scheduleNext_preserves_wf by blast
  thus ?thesis by (simp add: wf_ScheduleState_currTid_inSys_def) 
qed

text \<open>Thus, the result of a step always produces a state with currTid in the systemTids.
   That is, currTid is never the initTid.   This will let us conclude that
   the initTid only occurs in the initial state.\<close>

lemma systemStep_sysstate_tidInSys: 
  assumes wf_model: "wf_Model m"
      and wf_sys: "wf_System sys m"
      and wf_st1: "wf_SystemState m sys st1"
      and step: "systemStep sys st1 st2"
  shows "currTidSystemState st2 \<in> systemTids sys"
proof -
  \<comment> \<open>Name the intermediate elements of a system step\<close>
  obtain systemTasks1 systemChs1 taskState' tid tidAction tscs scheduleState2 systemTasks2 systemChs2 where
    p0: "systemTasks1 = systemTasks st1" and
    p1: "systemChs1 = systemChs st1" and
    p2: "scheduleState2 = scheduleNext (schedule sys) (scheduleState st1)" and
    p2a: "tid = (currTid scheduleState2)" and
    p3: "tidAction = action ((taskMap sys) $ tid)" and
    p4: "taskState' = systemTasks1 $ tid" and
    p5: "tscs = do_action (taskState', systemChs1) tidAction" and
    p5a: "systemTasks2 = systemTasks1 (tid \<mapsto> fst tscs)" and
    p5b: "systemChs2 = snd tscs" and
    p6: "st2 = mkSystemState systemTasks2 systemChs2 scheduleState2 systemTasks1 systemChs1"
    using step
    by (metis systemStep.simps)
  \<comment> \<open>By well-formedness properties of scheduleNext, we know currTid2 is in the system Tids\<close>
  from wf_sys wf_model wf_st1 wf_SystemState_def p1 p2 have 
    "tid \<in> systemTids sys"
    using scheduleNext_preserves_wf wf_ScheduleState_currTid_inSys_def p2a by blast
  thus ?thesis using p2a p6 by (simp add: mkSystemState_def)
qed

text \<open>A system step preserves well-formedness.\<close>

lemma systemStep_preserves_wellformedness: 
  assumes wf_model: "wf_Model m"
      and wf_sys: "wf_System sys m"
      and wf_st1: "wf_SystemState m sys st1"
      and step: "systemStep sys st1 st2"
  shows "wf_SystemState m sys st2"
proof -
  \<comment> \<open>Name the intermediate elements of a system step\<close>
  obtain systemTasks1 systemChs1 taskState' tid tidAction tscs scheduleState2 systemTasks2 systemChs2 where
    p0: "systemTasks1 = systemTasks st1" and
    p1: "systemChs1 = systemChs st1" and
    p2: "scheduleState2 = scheduleNext (schedule sys) (scheduleState st1)" and
    p2a: "tid = (currTid scheduleState2)" and
    p3: "tidAction = action ((taskMap sys) $ tid)" and
    p4: "taskState' = systemTasks1 $ tid" and
    p5: "tscs = do_action (taskState', systemChs1) tidAction" and
    p5a: "systemTasks2 = systemTasks1 (tid \<mapsto> fst tscs)" and
    p5b: "systemChs2 = snd tscs" and
    p6: "st2 = mkSystemState systemTasks2 systemChs2 scheduleState2 systemTasks1 systemChs1"
    using step
    by (metis systemStep.simps)
  \<comment> \<open>Since st1 is well-formed, the scheduleState for st1 is well-formed.\<close>
  from wf_st1 have wf_scheduleState_st1: "wf_ScheduleState sys (scheduleState st1)" 
    by (auto simp add: wf_SystemState_def)

  \<comment> \<open>The schedule state scheduleState' for st2 is well-formed because 
     scheduleNext preserves schedule state well-formedness,
     and the resulting currTid is in the systemTids\<close>
  from p2 p2a wf_scheduleState_st1 wf_sys wf_model
  have wf_scheduleState': 
     "wf_ScheduleState sys scheduleState2 
      \<and> wf_ScheduleState_currTid_inSys sys tid"
    using scheduleNext_preserves_wf by blast

  \<comment> \<open>wf_ChState\<close>

  \<comment> \<open>ChState is well-formed since the system is assumed well-formed and the actions of the well-formed system preserve state domains\<close>
  from wf_st1 p1 have wf_chState_st1: "wf_ChState (modelChIds m) systemChs1"
    by (auto simp add: wf_SystemState_def)

  from wf_chState_st1 wf_sys wf_scheduleState' p3 p5 p5b have wf_chState': "wf_ChState (modelChIds m) systemChs2"
    by (simp add: wf_ScheduleState_currTid_inSys_def wf_System_ActionsChState_def wf_System_def)

  \<comment> \<open>wf_SystemState_systemTasks_dom\<close>

  \<comment> \<open>st1 has a well-formed SystemState systemTasks domain\<close>
  have wf_SystemState_systemTasks_dom_st1: "wf_SystemState_systemTasks_dom m st1" 
    using wf_SystemState_def wf_st1 by auto
  \<comment> \<open>tid from schedule is in the domain\<close>
  have tidInDomst1: "tid \<in> dom systemTasks1"
    using p0 systemTids.simps wf_ScheduleState_currTid_inSys_def wf_SystemState_systemTasks_dom_def wf_SystemState_systemTasks_dom_st1 wf_System_TidsDom_def wf_System_def wf_scheduleState' wf_sys by blast
  \<comment> \<open>since tid is in systemTasks1's domain and the only update to systemTasks1 is using tid, the domains are the same\<close>
  have Domst1EqDomst2: "dom systemTasks1 = dom systemTasks2"
    using p5a tidInDomst1 by auto
  \<comment> \<open>transitively the domain of systemTasks2 is equivalent to the modelTids\<close>
  have Domst2EqModelTids: "(modelTids m) = dom systemTasks2"
    by (metis Domst1EqDomst2 p0 wf_SystemState_systemTasks_dom_def wf_SystemState_systemTasks_dom_st1)
  \<comment> \<open>systemTasks2 domain is equivalent the the systemTaks domain of st2 by the definition of the construction of the state\<close>
  from p6 have domPreservedInConstruction: "dom systemTasks2 = dom (systemTasks st2)"
    by (auto simp add: mkSystemState_def)  
  \<comment> \<open>the dom of st2's systemTasks is well-formed with respect to the model\<close>
  from wf_SystemState_def wf_st1 p0 p5a Domst2EqModelTids domPreservedInConstruction have wf_SystemState_systemTasks_dom_st2: "wf_SystemState_systemTasks_dom m st2"
    by (auto simp add: mkSystemState_def wf_SystemState_systemTasks_dom_def)

  \<comment> \<open>wf_SystemState_systemTasks\<close>

  \<comment> \<open>the var domain of the task's states of st1 is well-formed\<close>
  from wf_st1 p0 have wf_taskStates_st1: "wf_SystemState_systemTasks m st1"
    by (simp add: wf_SystemState_def)
  \<comment> \<open>the var domain of the task's states st2 is well-formed\<close>
  from wf_taskStates_st1 p0 p2a p4 wf_sys p2a wf_SystemState_systemTasks_dom_st2 have wf_taskStates_st2: "wf_SystemState_systemTasks m st2"
  proof (simp add: wf_SystemState_systemTasks_def)
    \<comment> \<open>deconstruct the definition of wf_SystemState_systemTasks to do an allI\<close>
    have r1: "\<And>tid. tid \<in> dom (systemTasks st2) \<longrightarrow> wf_TaskState (the (modelTaskDescrs m tid)) (the (systemTasks st2 tid))"
    proof -
      \<comment> \<open>fix tida as a fixed arbitrary value of tid\<close>
      fix tida
      \<comment> \<open>proof that the property holds for an arbitrary tid with impI\<close>
      show "tida \<in> dom (systemTasks st2) \<longrightarrow> wf_TaskState (the (modelTaskDescrs m tida)) (the (systemTasks st2 tida))"
      proof (rule impI)
        assume a1: "tida \<in> dom (systemTasks st2)"

        \<comment> \<open>tida must be in the domain of the systemTasks of st1 since we proved that in the last section\<close>
        have r3: "tida \<in> dom (systemTasks st1)"
          by (metis Domst1EqDomst2 a1 domPreservedInConstruction p0)

        \<comment> \<open>because tida is in the domain of systemTasks of st1 the task state tied to tida must be well-formed\<close>
        then have r4: "wf_TaskState (the (modelTaskDescrs m tida)) (the (systemTasks st1 tida))" 
          by (metis wf_SystemState_systemTasks_def wf_taskStates_st1)

        \<comment> \<open>trivially, tida is the currTid or it is not L.E.M.\<close>
        have "tida = tid \<or> tida \<noteq> tid" by auto

        \<comment> \<open>prove the thesis by disjE\<close>
        then show "wf_TaskState (the (modelTaskDescrs m tida)) (the (systemTasks st2 tida))" 
        proof (elim disjE)
          assume tidEq: "tida = tid"
  
          from mkSystemState_def have tscsEquiv: "(the (systemTasks st2 tida)) = (fst tscs)"
            by (metis SystemState.select_convs(1) fun_upd_same option.sel p5a p6 tidEq)

          \<comment> \<open>the domain of the taskMap is the same as the dom of the systemTasks of st1\<close>
          have taskMapEqsystemTasks_dom_st1: "dom (taskMap sys) = dom (systemTasks st1)"
            by (metis Domst1EqDomst2 Domst2EqModelTids p0 wf_System_TidsDom_def wf_System_def wf_sys)
  
          \<comment> \<open>instantiate the universally quantified property of actions that say that actions do not affect the var domain of tasks\<close>
          from this wf_sys have r2: "wf_TaskState ((modelTaskDescrs m) $ tida) (fst ((the (systemTasks st1 tida)), systemChs1)) 
                        \<longrightarrow>  wf_TaskState ((modelTaskDescrs m) $ tida) (fst ((action ((taskMap sys) $ tida)) ((the (systemTasks st1 tida)), systemChs1)))"
          by (metis r3 taskMapEqsystemTasks_dom_st1 wf_System_ActionsTaskState_def wf_System_def)

          \<comment> \<open>apply impE\<close>
          then have "wf_TaskState ((modelTaskDescrs m) $ tida) (fst ((action ((taskMap sys) $ tida)) ((the (systemTasks st1 tida)), systemChs1)))"
          by (metis r4 fst_conv)

          thus ?thesis
            using  p0 p3 p4 p5 tidEq tscsEquiv by auto 
  
        next
          assume tidNotEq: "tida \<noteq> tid"

          \<comment> \<open> because the action only acts on the tasks tied to tid, the other tasks will remain unaffected\<close>
          from mkSystemState_def have "(the (systemTasks st2 tida)) = (the (systemTasks st1 tida))"
            by (metis SystemState.select_convs(1) fun_upd_apply p0 p5a p6 tidNotEq)

          \<comment> \<open>because the tasks' states are not updated they remain well-formed\<close>
          thus ?thesis
            by (simp add: r4)
        qed
      qed
    qed
    from r1 have "\<forall>tid. tid \<in> dom (systemTasks st2) \<longrightarrow> wf_TaskState (the (modelTaskDescrs m tid)) (the (systemTasks st2 tid))"
      by simp
    thus "\<forall>tid\<in>dom (systemTasks st2). wf_TaskState (the (modelTaskDescrs m tid)) (the (systemTasks st2 tid))"
      by simp 
  qed

  \<comment> \<open>Conclusion\<close>

  from wf_scheduleState' wf_chState' wf_SystemState_systemTasks_dom_st2 wf_taskStates_st2 p6 show "wf_SystemState m sys st2" 
    by (auto simp add: wf_SystemState_def mkSystemState_def)
qed 

lemma multiStep_preserves_wellformedness: 
     "\<lbrakk>(systemStep sys)\<^sup>*\<^sup>* st1 st2; 
        wf_Model m;
        wf_System sys m;
        wf_SystemState m sys st1\<rbrakk> \<Longrightarrow> wf_SystemState m sys st2"
  apply (induction rule: rtranclp_induct)
  using systemStep_preserves_wellformedness by (auto+)

lemma systemReach_yields_wellformedness: 
  assumes model_wf: "wf_Model m"
     and sys_wf: "wf_System sys m"
     and reach: "systemReach sys st"
     and initState_wf: "wf_SystemState m sys (initSystemState sys)"
   shows "wf_SystemState m sys st"
proof - 
  from reach have 
    multiStep: "((systemStep sys)\<^sup>*\<^sup>* (initSystemState sys) st)" 
    by (simp add: systemReach_def)
  from sys_wf initState_wf multiStep show "wf_SystemState m sys st"
    using multiStep_preserves_wellformedness
    using model_wf by auto 
qed

end