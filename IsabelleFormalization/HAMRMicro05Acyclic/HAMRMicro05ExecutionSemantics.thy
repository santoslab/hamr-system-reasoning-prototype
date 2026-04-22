theory HAMRMicro05ExecutionSemantics
  imports HAMRMicro05Model
begin


section \<open>Definitions for Execution (Semantics)\<close>

subsection \<open>Single Step Execution\<close>

text \<open>Define a helper function to abstract the execution of the behavior of each
task.  This function just "runs" the action on the given store.\<close>

fun do_action :: " ('value TaskState \<times> 'value ChState) 
                 \<Rightarrow> 'value Action
                 \<Rightarrow> ('value TaskState \<times> 'value ChState)"

where "do_action tscs a = (a tscs)"

inductive systemStep for sys::"'value System"
                where
 stepTask: "\<lbrakk>
         \<comment> \<open>Non-deterministically pick a fireable transition, choice\<close>
         choice \<in> {s. s |\<subseteq>| (ready sysState) \<and> s \<in> (dom (nextRel sys))}; 
         \<comment> \<open>if choice is a task/component transition\<close>
         choice \<in> dom (activationMap sys);
         \<comment> \<open>update ready\<close>
         ready' = scheduleNext (nextRel sys) (ready sysState) choice;
         \<comment> \<open>get tid of task that correlated with choice\<close>
         tid = (activationMap sys) $ choice;
         \<comment> \<open>get the action for the task activated tied to choice\<close>
         tidAction = action ((taskMap sys) $ tid);
         \<comment> \<open>apply the action to the state\<close>
         tscs' = do_action ((systemTasks sysState) $ tid, (systemChs sysState)) tidAction;
         \<comment> \<open>create the new state\<close>
         sysState' = mkSystemState ((systemTasks sysState) (tid \<mapsto> (fst tscs'))) 
                                   (snd tscs') ready' (systemTasks sysState) (systemChs sysState)\<rbrakk>
         \<Longrightarrow> systemStep sys sysState sysState'"
| stepSkip: "\<lbrakk>
         \<comment> \<open>Non-deterministically pick a fireable transition, choice\<close>
         choice \<in> {s. s |\<subseteq>| (ready sysState) \<and> s \<in> (dom (nextRel sys))}; 
         \<comment> \<open>if choice is not a component/task transition\<close>
         choice \<notin> dom (activationMap sys);
         \<comment> \<open>update ready\<close>
         ready' = scheduleNext (nextRel sys) (ready sysState) choice;
         \<comment> \<open>create the new state\<close>
         sysState' = mkSystemState (systemTasks sysState) (systemChs sysState) ready' 
                                   (systemTasks sysState) (systemChs sysState)\<rbrakk>
         \<Longrightarrow> systemStep sys sysState sysState'"

text \<open>If you can take an execution step from st1 to st2, the previous task and channel states stored in
      st2 are the current task and channel states of st1.\<close>

lemma stepCurrentStorePreviousStore:
  assumes step: "systemStep sys st1 st2"
  shows "systemTasks st1 = previousSystemTasks st2 \<and> systemChs st1 = previousSystemChs st2"
  using assms
proof (cases)
  case (stepTask choice ready' tid tidAction tscs')

  assume a1: "choice \<in> {s. s |\<subseteq>| ready st1 \<and> s \<in> dom (nextRel sys)}"
  assume a2: "choice \<in> dom (activationMap sys)"
  assume a3: "ready' = scheduleNext (nextRel sys) (ready st1) choice"
  assume a4: "tid = the (activationMap sys choice)"
  assume a5: "tidAction = action (the (taskMap sys tid))"
  assume a6: "tscs' = do_action (the (systemTasks st1 tid), systemChs st1) tidAction"
  assume a7: "st2 = mkSystemState ((systemTasks st1)(tid \<mapsto> fst tscs')) (snd tscs') ready' (systemTasks st1) (systemChs st1)"

  from a7 show ?thesis by (auto simp add: mkSystemState_def)
next
  case (stepSkip choice ready')

  assume a1: "choice \<in> {s. s |\<subseteq>| ready st1 \<and> s \<in> dom (nextRel sys)}"
  assume a2: "choice \<notin> dom (activationMap sys)"
  assume a3: "ready' = scheduleNext (nextRel sys) (ready st1) choice"
  assume a4: "st2 = mkSystemState (systemTasks st1) (systemChs st1) ready' (systemTasks st1) (systemChs st1)"

  from a4 show ?thesis by (auto simp add: mkSystemState_def)
qed  

subsection \<open>Multi-Step and System Execution\<close>

definition systemReach :: "'store System \<Rightarrow> 'store SystemState \<Rightarrow> bool" where 
 "systemReach sys st = ((systemStep sys)\<^sup>*\<^sup>* (initSystemState sys) st)"

text \<open>A system step preserves well-formedness.\<close>

lemma systemStep_preserves_wellformedness: 
  assumes wf_model: "wf_Model m"
      and wf_sys: "wf_System sys m"
      and nextAssms: "nextRel_Assumptions sys m"
      and wf_st1: "wf_SystemState m sys st1"
      and step: "systemStep sys st1 st2"
    shows "wf_SystemState m sys st2"
  using step
proof (cases)
  case (stepTask choice ready' tid tidAction tscs')

  assume a1: "choice \<in> {s. s |\<subseteq>| ready st1 \<and> s \<in> dom (nextRel sys)}"
  assume a2: "choice \<in> dom (activationMap sys)"
  assume a3: "ready' = scheduleNext (nextRel sys) (ready st1) choice"
  assume a4: "tid = the (activationMap sys choice)"
  assume a5: "tidAction = action (the (taskMap sys tid))"
  assume a6: "tscs' = do_action (the (systemTasks st1 tid), systemChs st1) tidAction"
  assume a7: "st2 = mkSystemState ((systemTasks st1)(tid \<mapsto> fst tscs')) (snd tscs') ready' (systemTasks st1) (systemChs st1)"

  \<comment> \<open>tid must be in the range of the activation map\<close>
  from a2 a4 have tid_in_am: "tid \<in> ran (activationMap sys)"
    by (simp add: map_some_val ranI)

  \<comment> \<open>tid must a Tid of the system\<close>
  from a2 a4 wf_sys tid_in_am have tid_in_sys: "tid \<in> systemTids sys"
    by (auto simp add: wf_System_ActivationMap_def wf_System_def)

  \<comment> \<open>wf_ChState\<close>
  from wf_st1 have wf_chState_st1: "wf_ChState (modelChIds m) (systemChs st1)"
    by (auto simp add: wf_SystemState_def)

  from wf_chState_st1 wf_sys a5 a6 tid_in_sys have wf_chState': "wf_ChState (modelChIds m) (systemChs st2)"
    by (simp add: wf_System_ActionsChState_def wf_System_def a7 mkSystemState_def)

  \<comment> \<open>wf_TaskState_dom\<close>

  \<comment> \<open>the domain of the systemTasks is well-formed\<close>
  have wf_SystemState_systemTasks_dom_st1: "wf_SystemState_systemTasks_dom m st1" 
    using wf_SystemState_def wf_st1 by auto

  \<comment> \<open>the TID of the task state being updated is in the domain of systemTasks st1\<close>
  from wf_st1 tid_in_sys wf_sys have tidInDomst1: "tid \<in> dom (systemTasks st1)"
    by (simp add: wf_SystemState_def wf_SystemState_systemTasks_dom_def wf_System_def wf_System_TaskMap_def)

  \<comment> \<open>this implies that the two domains are equal since the update done for st2 use a taskID that is
      already in the domain of st1\<close>
  have Domst1EqDomst2: "dom (systemTasks st1) = dom (systemTasks st2)"
    using a7 tidInDomst1 by (auto simp add: mkSystemState_def)

  \<comment> \<open>this implies that the domain of systemTasks is well-formed\<close>
  from wf_st1 a7 Domst1EqDomst2 have wf_SystemState_systemTasks_dom_st2: "wf_SystemState_systemTasks_dom m st2"
    by (auto simp add: wf_SystemState_def wf_SystemState_systemTasks_dom_def)

  \<comment> \<open>wf_TaskState\<close>

  \<comment> \<open>The task states of st1 are well-formed\<close>
  from wf_st1 a7 have wf_taskStates_st1: "wf_SystemState_systemTasks m st1"
    by (simp add: wf_SystemState_def mkSystemState_def)

  \<comment> \<open>All tasks states in st2 are the tasks stated in the model\<close>
  from Domst1EqDomst2 wf_st1 have Domst2EqModelTids: "(modelTids m) = dom (systemTasks st2)"
    by (auto simp add: wf_SystemState_def wf_SystemState_systemTasks_dom_def)

  \<comment> \<open>The task states of st2 are well-formed\<close>
  from wf_taskStates_st1 a4 wf_sys wf_SystemState_systemTasks_dom_st2 have wf_taskStates_st2: "wf_SystemState_systemTasks m st2"
  proof (simp add: wf_SystemState_systemTasks_def)
    \<comment> \<open>all task states of st2 are well-formed\<close>
    have r1: "\<And>tid. tid \<in> dom (systemTasks st2) \<longrightarrow> wf_TaskState (the (modelTaskDescrs m tid)) (the (systemTasks st2 tid))"
    proof -
      fix tida
       \<comment> \<open>given task A has a task state in st2, the task state of st2 must be well-formed\<close>
      show "tida \<in> dom (systemTasks st2) \<longrightarrow> wf_TaskState (the (modelTaskDescrs m tida)) (the (systemTasks st2 tida))"
      proof (rule impI)
        \<comment> \<open>task A has a task state in st2\<close>
        assume a1: "tida \<in> dom (systemTasks st2)"
        \<comment> \<open>task A has a task state in st1\<close>
        have r3: "tida \<in> dom (systemTasks st1)"
          by (auto simp add: Domst1EqDomst2 a1)
        \<comment> \<open>task A has a well-formed task state in st1 since all task states in st1 only refer to 
            the local variable defined in the task description \<close>
        from r3 wf_st1 have r4: "wf_TaskState (the (modelTaskDescrs m tida)) (the (systemTasks st1 tida))"
          by (auto simp add: wf_SystemState_def wf_SystemState_systemTasks_def wf_taskStates_st1)

        \<comment> \<open>task A is either the current task or it isn't\<close>
        have "tida = tid \<or> tida \<noteq> tid" by auto
        then show "wf_TaskState (the (modelTaskDescrs m tida)) (the (systemTasks st2 tida))"
        proof (elim disjE)
          \<comment> \<open>task A is the current task\<close>
          assume tidEq: "tida = tid"

          \<comment> \<open>the task state produced by executing the task is the same as the task state of Task A
              in st2 by construction\<close>
          from a7 tidEq have tscsEquiv: "(the (systemTasks st2 tida)) = (fst tscs')"
            by (auto simp add: mkSystemState_def)

          \<comment> \<open>the domain of the taskMap is the same as the dom of the systemTasks of st1\<close>
          from wf_sys have taskMapEqsystemTasks_dom_st1: "dom (taskMap sys) = dom (systemTasks st1)"
            using Domst2EqModelTids by (simp add: wf_System_def wf_System_TaskMap_def Domst1EqDomst2)

          \<comment> \<open>task A must be tasks of the system\<close>
          have r5: "tida \<in> (dom (taskMap sys))"
            using tidEq tid_in_sys by auto

          \<comment> \<open>if task A has a well-formed task state then applying the action tied to task A results
              in a well-formed task state\<close>
          from r5 have r6: "\<forall>tscs. 
             wf_TaskState ((modelTaskDescrs m) $ (taskId ((taskMap sys) $ tida))) (fst tscs) \<longrightarrow>  
             wf_TaskState ((modelTaskDescrs m) $ (taskId ((taskMap sys) $ tida))) 
                          (fst ((action ((taskMap sys) $ tida)) tscs))"
            using wf_System_ActionsTaskState_def wf_System_def wf_sys by blast

          \<comment> \<open>if task A has a well-formed task state then applying the action tied to task A results
              in a well-formed task state given the task and channel states of st1\<close>
          from r6 have r7: "wf_TaskState ((modelTaskDescrs m) $ (taskId ((taskMap sys) $ tida))) (fst ((the (systemTasks st1 tida)), (systemChs st1))) \<longrightarrow>  
                           wf_TaskState ((modelTaskDescrs m) $ (taskId ((taskMap sys) $ tida))) 
                           (fst ((action ((taskMap sys) $ tida)) ((the (systemTasks st1 tida)), (systemChs st1))))"
            by blast

          \<comment> \<open>reduce (taskId ((taskMap sys) $ tida)) to tida\<close>
          from r5 r7 wf_sys have r8: "wf_TaskState ((modelTaskDescrs m) $ tida) (the (systemTasks st1 tida)) \<longrightarrow>  
                           wf_TaskState ((modelTaskDescrs m) $ (taskId ((taskMap sys) $ tida))) 
                           (fst ((action ((taskMap sys) $ tida)) ((the (systemTasks st1 tida)), (systemChs st1))))"
            by (simp add: wf_System_TaskMap_def wf_System_def)

          \<comment> \<open>the task state of task A after applying the action tied to task A is well-formed\<close>
          from this r4 r5  have "wf_TaskState ((modelTaskDescrs m) $ tida) (fst ((action ((taskMap sys) $ tida)) ((the (systemTasks st1 tida)), (systemChs st1))))"
            by (metis wf_System_TaskMap_def wf_System_def wf_sys)

          thus ?thesis
            using a5 a6 tidEq tscsEquiv by auto
        next
          \<comment> \<open>task A is not the current task\<close>
          assume tidNotEq: "tida \<noteq> tid"

          \<comment> \<open>since the task state will not be updated it is still well-formed\<close>
          from a7 wf_st1 have "(the (systemTasks st2 tida)) = (the (systemTasks st1 tida))"
            apply (auto simp add: mkSystemState_def)
            using tidNotEq by force

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

  \<comment> \<open>Reachable schedule state\<close>

  \<comment> \<open>st1 has a reachable schedule state from {|START|}\<close>
  from wf_st1 have reachable_st1: "wf_SystemState_Reach sys m st1"
    by (simp add: wf_SystemState_def)

  \<comment> \<open>st2 has a reachable schedule state from {|START|}\<close>
  from this a3 a7 have reachable_st2: "wf_SystemState_Reach sys m st2"
  proof (simp add: wf_SystemState_Reach_def mkSystemState_def)
    assume a11: "scheduleReach (nextRel sys) {|modelStartRid m|} (ready st1)"
    assume a12: "ready' = ready st1 |-| choice |\<union>| the (nextRel sys choice)"
    assume a13: "st2 = \<lparr>systemTasks = (systemTasks st1)(tid \<mapsto> fst tscs'), 
                        systemChs = snd tscs', 
                        ready = ready st1 |-| choice |\<union>| the (nextRel sys choice), 
                        previousSystemTasks = systemTasks st1, 
                        previousSystemChs = systemChs st1\<rparr>"

    \<comment> \<open>the choice of transition should be in the set of fireable transitions\<close>
    have r1: "choice \<in> {s. s |\<subseteq>| (ready st1) \<and> s \<in> (dom (nextRel sys))}"
      using a1 by auto
    \<comment> \<open>the schedule state of st2 should be the result of updating the schedule state of st1
        with choice\<close>
    from a12 a13 have r3: "ready st1 |-| choice |\<union>| the (nextRel sys choice) = ready st2"
      by simp
    \<comment> \<open>because the update is possible, there should be a schedule step from (ready st1) to (ready st2)\<close>
    from r1 r3 have "scheduleStep (nextRel sys) (ready st1) (ready st2)"
      apply (simp add: scheduleStep_def)
      by auto
    \<comment> \<open>because the schedule state of st1 is reachable and the schedule can go from (ready st1) to (ready st2),
        the schedule state of st2 is reachable\<close>
    from this a11 have "scheduleReach (nextRel sys) {|modelStartRid m|} (ready st2)"
      by (simp add: scheduleReach_def)
    \<comment> \<open>we can state an equivalent statement using the schedule state update described by st2\<close>
    from this r3 show "scheduleReach (nextRel sys) {|modelStartRid m|} (ready st1 |-| choice |\<union>| the (nextRel sys choice))"
      by auto
  qed

  \<comment> \<open>No Deadlock\<close>        

  \<comment> \<open>the schedule state of st1 conditionally does not deadlock\<close>
  from wf_st1 have wf_SystemState_NoDeadlock_st1: "wf_SystemState_ConditionalDeadlock sys m st1" 
    by (simp add: wf_SystemState_def)

  \<comment> \<open>get only the assumptions from the nextRel assumptions for this proof to avoid over cluttering\<close>
  from nextAssms have NoDeadlockAndOptToCompl: "wf_System_NextRel_OptToComplete sys m \<and> wf_System_NextRel_NoDeadTransitions sys m"
    by (simp add: nextRel_Assumptions_def)

  \<comment> \<open>the schedule state of st2 conditionally does not deadlock\<close>
  from wf_SystemState_NoDeadlock_st1 a3 a7 NoDeadlockAndOptToCompl have wf_SystemState_NoDeadlock_st2: "wf_SystemState_ConditionalDeadlock sys m st2"
    apply (unfold mkSystemState_def)
    proof (erule conjE)
      assume a11: "wf_SystemState_ConditionalDeadlock sys m st1"
      assume a12: "ready' = scheduleNext (nextRel sys) (ready st1) choice"
      assume a13: "st2 = \<lparr>systemTasks = (systemTasks st1)(tid \<mapsto> fst tscs'), 
                          systemChs = snd tscs',
                          ready = ready', 
                          previousSystemTasks = systemTasks st1, 
                          previousSystemChs = systemChs st1\<rparr>"
      assume a14: "wf_System_NextRel_OptToComplete sys m"
      assume a15: "wf_System_NextRel_NoDeadTransitions sys m"

      show "wf_SystemState_ConditionalDeadlock sys m st2"
        apply (simp add: wf_SystemState_ConditionalDeadlock_def)
      proof auto
        \<comment> \<open>if a place exist in the schedule state of st2 and there is no available moves, then
            the place must be END\<close>

        fix x
        assume a113: "x |\<in>| ready st2"
        assume a114: "card {s. s |\<subseteq>| ready st2 \<and> s \<in> dom (nextRel sys)} = 0"

        show "x = modelEndRid m"
        proof (rule ccontr)
          assume a: "x \<noteq> modelEndRid m"

          \<comment> \<open>the number of fireable transitions must be finite\<close>
          have fin: "finite {s. s |\<subseteq>| (ready st2) \<and> s \<in> (dom (nextRel sys))}"
            using wf_System_NextRel_def wf_System_def wf_sys by fastforce

          \<comment> \<open>Because of the proper completion requirement, END cannot be in the schedule state\<close>
          from a a113 have "modelEndRid m |\<notin>| (ready st2)"
            by (metis fsingleton_iff nextAssms nextRel_Assumptions_def reachable_st2 
                      wf_SystemState_Reach_def wf_System_NextRel_ProperComplete_def)

          \<comment> \<open>this means that the schedule state of st2 cannot equal the final state\<close>
          then have noteq:"{|modelEndRid m|} \<noteq> (ready st2)" by auto

          \<comment> \<open>Because st2 has a reachable schedule state and it is not the final state, 
              then the schedule state must be able to reach the end state due to the 
              option-to-complete requirement\<close>
          from this have reach: "scheduleReach (nextRel sys) (ready st2) {|modelEndRid m|}"
            by (metis a14 reachable_st2 wf_SystemState_Reach_def wf_System_NextRel_OptToComplete_def)

          \<comment> \<open>if schst1 is able to reach schst2 and schst1 does not equal schst2, then there
              must exist a schst3 that does not equal schst1 such that the schedule is able to step
              from schst1 to schst3\<close>
          have "\<forall>schst1 schst2. (schst1 \<noteq> schst2 \<and> scheduleReach (nextRel sys) schst1 schst2 
                 \<longrightarrow> (\<exists>schst3. schst1 \<noteq> schst3 \<and> scheduleStep (nextRel sys) schst1 schst3))"
            by (smt (verit, del_insts) converse_rtranclpE rtranclp_induct scheduleReach_def)

          \<comment> \<open>because of this, there must exist a schst not equal to the schedule state of st2 such
              that the schedule can step from the schedule state of st2 to schst\<close>
          from this reach noteq have "\<exists>schst. schst \<noteq> (ready st2) \<and> scheduleStep (nextRel sys) (ready st2) schst"
            apply (simp add: scheduleReach_def scheduleStep_def)
            by metis

          \<comment> \<open>there must be a fireable transition in the schedule state of st2\<close>
          then have "\<exists> t. t \<in> {s. s |\<subseteq>| (ready st2) \<and> s \<in> (dom (nextRel sys))}"
            using scheduleStep_def by auto

          \<comment> \<open>this implies that the set of fireable transitions for st2 must be non-empty\<close>
          from this card_0_eq a114 fin have "card {s. s |\<subseteq>| (ready st2) \<and> s \<in> (dom (nextRel sys))} > 0"
            by auto

          \<comment> \<open>this is a contradiction since it was assumed that there is no available moves for st2\<close>
          from this a114 show False by auto
        qed
      next
        \<comment> \<open>if there are available moves in st2 and the {|END|} is in the schedule state of st2
            then this is a contradiction\<close>
        assume a112: "0 < card {s. s |\<subseteq>| {|modelEndRid m|} \<and> s \<in> dom (nextRel sys)}"
        assume a113: "ready st2 = {|modelEndRid m|}"

        \<comment> \<open>{|END|} is not a set in places tied to a transition\<close>
        from wf_sys have "nextRel sys {|modelEndRid m|} = None"
          apply (simp add: domIff wf_System_NextRel_SourceAndSink_def wf_System_NextRel_def wf_System_def)
          by blast
          
        thus  False
          by (metis (mono_tags, lifting) Collect_empty_eq a112 card.empty domIff fsubset_fsingletonD 
                                         linorder_neq_iff wf_System_NextRel_def wf_System_def wf_sys)
      next
        \<comment> \<open>if there are no fireable transitions in st2, END must be in the schedule state of st2\<close>

        assume a113: "card {s. s |\<subseteq>| ready st2 \<and> s \<in> dom (nextRel sys)} = 0"  
        show "modelEndRid m |\<in>| ready st2"
        proof (rule ccontr)
          assume a: "modelEndRid m |\<notin>| ready st2"

          \<comment> \<open>if END is not in the schedule state of st2, then the schedule state cannot
              be the final state\<close>
          then have noteq:"{|modelEndRid m|} \<noteq> (ready st2)" by auto

          \<comment> \<open>the number of fireable transitions  must be finite\<close>
          have fin: "finite {s. s |\<subseteq>| (ready st2) \<and> s \<in> (dom (nextRel sys))}"
            using wf_System_NextRel_def wf_System_def wf_sys by fastforce

          \<comment> \<open>because (ready st2) is reachable from {|START|} and it is {|END|}, then the schedule must
              be able to reach the {|END|} due to the option-to-complete requirement\<close>
          from this have reach: "scheduleReach (nextRel sys) (ready st2) {|modelEndRid m|}"
            by (metis a14 reachable_st2 wf_SystemState_Reach_def wf_System_NextRel_OptToComplete_def)

          \<comment> \<open>if schst1 is able to reach schst2 and schst1 does not equal schst2, then there
              must exist a schst3 that does not equal schst1 such that the schedule is able to step
              from schst1 to schst3\<close>
          have "\<forall>schst1 schst2. (schst1 \<noteq> schst2 \<and> scheduleReach (nextRel sys) schst1 schst2 
                 \<longrightarrow> (\<exists>schst3. schst1 \<noteq> schst3 \<and> scheduleStep (nextRel sys) schst1 schst3))"
            by (smt (verit, del_insts) converse_rtranclpE rtranclp_induct scheduleReach_def)

          \<comment> \<open>because of this, there must exist a schst not equal to the schedule state of st2 such
              that the schedule can step from the schedule state of st2 to schst\<close>
          from this reach noteq have "\<exists>schedst. schedst \<noteq> (ready st2) \<and> scheduleStep (nextRel sys) (ready st2) schedst"
            apply (simp add: scheduleReach_def scheduleStep_def)
            by metis

          \<comment> \<open>there must be an available move for the schedule state of st2\<close>
          then have "\<exists> t. t \<in> {s. s |\<subseteq>| (ready st2) \<and> s \<in> (dom (nextRel sys))}"
            using scheduleStep_def by auto

          \<comment> \<open>this implies that the set of available moves for st2 must be non-empty\<close>
          from this card_0_eq fin have "card {s. s |\<subseteq>| (ready st2) \<and> s \<in> (dom (nextRel sys))} > 0"
            by auto

          \<comment> \<open>this is a contradiction since it was assumed that there is no fireable transitions for st2\<close>
          from this a113 show False by auto
        qed
      qed
    qed

    \<comment> \<open>wf_SystemState_ReadySub\<close>

    \<comment> \<open>The schedule state of st1 is a subset of the model Ready IDs\<close>
    have rs1: "wf_SystemState_ReadySub sys m st1"
      using wf_SystemState_def wf_st1 by auto

    \<comment> \<open>The schedule state of st2 is a subset of the model Ready IDs\<close>
    from this a1 a3 a7 have wf_SystemState_ReadySub_st2: "wf_SystemState_ReadySub sys m st2" 
      apply (auto simp add: wf_SystemState_ReadySub_def mkSystemState_def)
    proof -
      fix x y
      assume r1subRIDS: "ready st1 |\<subseteq>| modelReadyIds m"
      assume rUpdate: "ready' = ready st1 |-| choice |\<union>| y"
      assume newSt2: "st2 = \<lparr>systemTasks = (systemTasks st1)(tid \<mapsto> fst tscs'), 
                             systemChs = snd tscs', 
                             ready = ready st1 |-| choice |\<union>| y, 
                             previousSystemTasks = systemTasks st1, 
                             previousSystemChs = systemChs st1\<rparr>"
      assume choiceInR1: "choice |\<subseteq>| ready st1"
      assume yMove: "nextRel sys choice = Some y"
      assume xInY: "x |\<in>| y"

      \<comment> \<open>(ready st1) minus the set of in places of choice is a subset of the model RIDs\<close>
      have "ready st1 |-| choice |\<subseteq>| modelReadyIds m"
        using r1subRIDS by auto 

      \<comment> \<open>the set of out places of choice are a subset of the model rids\<close>
      from wf_sys have "y |\<subseteq>| modelReadyIds m"
        apply (simp add: wf_System_def wf_System_NextRel_def wf_System_NextRel_RanUnion_def)
        by (meson UnI2 ranI yMove)

      \<comment> \<open>all out places of choice are in the NextRel are model rids\<close>
      thus "x |\<in>| modelReadyIds m"
        using xInY by auto
    qed
      
  from wf_chState' wf_SystemState_systemTasks_dom_st2 wf_taskStates_st2 wf_SystemState_NoDeadlock_st2 show ?thesis
    by (simp add: wf_SystemState_def reachable_st2 wf_SystemState_ReadySub_st2)
next
  case (stepSkip choice ready')

  assume a1: "choice \<in> {s. s |\<subseteq>| ready st1 \<and> s \<in> dom (nextRel sys)}"
  assume a2: "choice \<notin> dom (activationMap sys)"
  assume a3: "ready' = scheduleNext (nextRel sys) (ready st1) choice"
  assume a4: "st2 = mkSystemState (systemTasks st1) (systemChs st1) ready' (systemTasks st1) (systemChs st1)"

  \<comment> \<open>the channel state of st2 is well formed\<close>
  from a4 wf_sys have wf_chState': "wf_ChState (modelChIds m) (systemChs st2)"
    apply (auto simp add: mkSystemState_def)
    using wf_SystemState_def wf_st1 by auto

  \<comment> \<open>the task states of st2 are well formed\<close>
  from wf_st1 a4 have wf_SystemState_systemTasks_dom_st2: "wf_SystemState_systemTasks_dom m st2"
    by (simp add: mkSystemState_def wf_SystemState_def wf_SystemState_systemTasks_dom_def)

  from a4 wf_sys wf_SystemState_systemTasks_dom_st2 have wf_taskStates_st2: "wf_SystemState_systemTasks m st2"
    apply (auto simp add: mkSystemState_def)
    by (metis SystemState.select_convs(1) wf_SystemState_def wf_SystemState_systemTasks_def wf_st1)
  
  \<comment> \<open>Reachable schedule state\<close>

  \<comment> \<open>st1 has a reachable schedule state from {|START|}\<close>
  from wf_st1 have reachable_st1: "wf_SystemState_Reach sys m st1"
    by (simp add: wf_SystemState_def)

  \<comment> \<open>st2 has a reachable schedule state from {|START|}\<close>
  from this a3 a4 have reachable_st2: "wf_SystemState_Reach sys m st2"
  proof (simp add: wf_SystemState_Reach_def mkSystemState_def)
    assume a11: "scheduleReach (nextRel sys) {|modelStartRid m|} (ready st1)"
    assume a12: "ready' = ready st1 |-| choice |\<union>| the (nextRel sys choice)"
    assume a13: "st2 = \<lparr>systemTasks = systemTasks st1, 
                        systemChs = systemChs st1, 
                        ready = ready st1 |-| choice |\<union>| the (nextRel sys choice), 
                        previousSystemTasks = systemTasks st1,
                        previousSystemChs = systemChs st1\<rparr>"
    \<comment> \<open>the choice of transition should be in the set of fireable transitions\<close>
    have r1: "choice \<in> {s. s |\<subseteq>| (ready st1) \<and> s \<in> (dom (nextRel sys))}"
      using a1 by auto
    \<comment> \<open>the schedule state of st2 should be the result of updating the schedule state of st1
        with choice\<close>
    from a12 a13 have r3: "ready st1 |-| choice |\<union>| the (nextRel sys choice) = ready st2"
      by simp
    \<comment> \<open>because the update is correct, there should be a schedule step from (ready st1) to (ready st2)\<close>
    from r1 r3 have "scheduleStep (nextRel sys) (ready st1) (ready st2)"
      apply (simp add: scheduleStep_def)
      by auto
    \<comment> \<open>because the schedule state of st1 is reachable and the schedule can go from (ready st1) to (ready st2),
        the schedule state of st2 is reachable\<close>
    from this a11 have "scheduleReach (nextRel sys) {|modelStartRid m|} (ready st2)"
      by (simp add: scheduleReach_def)
    \<comment> \<open>we can state an equivalent statement using the schedule state update described by st2\<close>
    from this r3 show "scheduleReach (nextRel sys) {|modelStartRid m|} (ready st1 |-| choice |\<union>| the (nextRel sys choice))"
      by auto
  qed


  \<comment> \<open>No Deadlock\<close>

  \<comment> \<open>the schedule state of the schedule state of st1 conditionally does not deadlock\<close>
  from wf_st1 have wf_SystemState_NoDeadlock_st1: "wf_SystemState_ConditionalDeadlock sys m st1" 
    by (simp add: wf_SystemState_def)

  \<comment> \<open>get only the assumptions from the nextRel assumptions for this proof to avoid over cluttering\<close>
  from nextAssms have NoDeadlockAndOptToCompl: "wf_System_NextRel_OptToComplete sys m \<and> wf_System_NextRel_NoDeadTransitions sys m"
    by (simp add: nextRel_Assumptions_def)

  \<comment> \<open>the schedule state of st2 conditionally does not deadlock\<close>
  from wf_SystemState_NoDeadlock_st1 a3 a4 NoDeadlockAndOptToCompl have wf_SystemState_NoDeadlock_st2: "wf_SystemState_ConditionalDeadlock sys m st2"
    apply (unfold mkSystemState_def)
    proof (erule conjE)
      assume a11: "wf_SystemState_ConditionalDeadlock sys m st1"
      assume a12: "ready' = scheduleNext (nextRel sys) (ready st1) choice"
      assume a13: "st2 = \<lparr>systemTasks = systemTasks st1, systemChs = systemChs st1, 
                          ready = ready', 
                          previousSystemTasks = systemTasks st1, 
                          previousSystemChs = systemChs st1\<rparr>"
      assume a14: "wf_System_NextRel_OptToComplete sys m"
      assume a15: "wf_System_NextRel_NoDeadTransitions sys m"

      show "wf_SystemState_ConditionalDeadlock sys m st2"
        apply (simp add: wf_SystemState_ConditionalDeadlock_def)
      proof auto
        \<comment> \<open>if a value exist in the schedule state of st2 and their is no available moves, the
            the value must be END rid\<close>

        fix x
        assume a113: "x |\<in>| ready st2"
        assume a114: "card {s. s |\<subseteq>| ready st2 \<and> s \<in> dom (nextRel sys)} = 0"

        show "x = modelEndRid m"
        proof (rule ccontr)
          assume a: "x \<noteq> modelEndRid m"

          \<comment> \<open>the number of fireable transitions must be finite\<close>
          have fin: "finite {s. s |\<subseteq>| (ready st2) \<and> s \<in> (dom (nextRel sys))}"
            using wf_System_NextRel_def wf_System_def wf_sys by fastforce

          \<comment> \<open>because of the proper completion requirement, the END cannot be in the schedule state\<close>
          from a a113 have "modelEndRid m |\<notin>| (ready st2)"
            by (metis fsingleton_iff nextAssms nextRel_Assumptions_def reachable_st2 
                      wf_SystemState_Reach_def wf_System_NextRel_ProperComplete_def)

          \<comment> \<open>this means that the schedule state of st2 cannot equal the final state\<close>
          then have noteq:"{|modelEndRid m|} \<noteq> (ready st2)" by auto

          \<comment> \<open>because the schedule state of st2 is reachable form {|START|} and it is not the final state, 
              the schedule state must be able to reach {|END|} state due to the option-to-complete requirement\<close>
          from this have reach: "scheduleReach (nextRel sys) (ready st2) {|modelEndRid m|}"
            by (metis a14 reachable_st2 wf_SystemState_Reach_def wf_System_NextRel_OptToComplete_def)

          \<comment> \<open>if schst1 is able to reach schst2 and schst1 does not equal schst2, then there
              must exist a schst3 that does not equal schst1 such that the schedule is able to step
              from schst1 to schst3\<close>
          have "\<forall>schst1 schst2. (schst1 \<noteq> schst2 \<and> scheduleReach (nextRel sys) schst1 schst2 
                 \<longrightarrow> (\<exists>schst3. schst1 \<noteq> schst3 \<and> scheduleStep (nextRel sys) schst1 schst3))"
            by (smt (verit, del_insts) converse_rtranclpE rtranclp_induct scheduleReach_def)

          \<comment> \<open>because of this, there must exist a schst not equal to the schedule state of st2 such
              that the schedule can step from the schedule state of st2 to schst\<close>
          from this reach noteq have "\<exists>schst. schst \<noteq> (ready st2) \<and> scheduleStep (nextRel sys) (ready st2) schst"
            apply (simp add: scheduleReach_def scheduleStep_def)
            by metis

          \<comment> \<open>there must be a fireable transition for the schedule state of st2\<close>
          then have "\<exists> t. t \<in> {s. s |\<subseteq>| (ready st2) \<and> s \<in> (dom (nextRel sys))}"
            using scheduleStep_def by auto

          \<comment> \<open>this implies that the set of fireable transitions for st2 must be non-empty\<close>
          from this card_0_eq a114 fin have "card {s. s |\<subseteq>| (ready st2) \<and> s \<in> (dom (nextRel sys))} > 0"
            by auto

          \<comment> \<open>this is a contradiction since it was assumed that there is no fireable transitions for st2\<close>
          from this a114 show False by auto
        qed
      next
        \<comment> \<open>if there are fireable transitions in (ready st2) and the END is in the schedule state of st2
            then this is a contradiction\<close>
        assume a112: "0 < card {s. s |\<subseteq>| {|modelEndRid m|} \<and> s \<in> dom (nextRel sys)}"
        assume a113: "ready st2 = {|modelEndRid m|}"

        from wf_sys have "nextRel sys {|modelEndRid m|} = None"
          apply (simp add: domIff wf_System_NextRel_SourceAndSink_def wf_System_NextRel_def wf_System_def)
          by blast

        thus False
          by (metis (mono_tags, lifting) Collect_empty_eq a112 card.empty domIff fsubset_fsingletonD 
                                         linorder_neq_iff wf_System_NextRel_def wf_System_def wf_sys)
      next
        \<comment> \<open>if there are no fireable transitions in st2 the END must be in the schedule state of st2\<close>

        assume a113: "card {s. s |\<subseteq>| ready st2 \<and> s \<in> dom (nextRel sys)} = 0"  
        show "modelEndRid m |\<in>| ready st2"
        proof (rule ccontr)
          assume a: "modelEndRid m |\<notin>| ready st2"

          \<comment> \<open>if the END is not in the schedule state of st2, then the schedule state cannot
              be the final state\<close>
          then have noteq:"{|modelEndRid m|} \<noteq> (ready st2)" by auto

          \<comment> \<open>the number of fireable transitions must be finite\<close>
          have fin: "finite {s. s |\<subseteq>| (ready st2) \<and> s \<in> (dom (nextRel sys))}"
            using wf_System_NextRel_def wf_System_def wf_sys by fastforce

          \<comment> \<open>because (ready st2) is reachable from {|START|} and it is not the final state, 
              the schedule state must be able to reach the {|END|} due to the option-to-complete requirement\<close>
          from this have reach: "scheduleReach (nextRel sys) (ready st2) {|modelEndRid m|}"
            by (metis a14 reachable_st2 wf_SystemState_Reach_def wf_System_NextRel_OptToComplete_def)

          \<comment> \<open>if schst1 is able to reach schst2 and schst1 does not equal schst2, then there
              must exist a schst3 that does not equal schst1 such that the schedule is able to step
              from schst1 to schst3\<close>
          have "\<forall>schst1 schst2. (schst1 \<noteq> schst2 \<and> scheduleReach (nextRel sys) schst1 schst2 
                 \<longrightarrow> (\<exists>schst3. schst1 \<noteq> schst3 \<and> scheduleStep (nextRel sys) schst1 schst3))"
            by (smt (verit, del_insts) converse_rtranclpE rtranclp_induct scheduleReach_def)

          \<comment> \<open>because of this, there must exist a schst not equal to the schedule state of st2 such
              that the schedule can step from the schedule state of st2 to schst\<close>
          from this reach noteq have "\<exists>schedst. schedst \<noteq> (ready st2) \<and> scheduleStep (nextRel sys) (ready st2) schedst"
            apply (simp add: scheduleReach_def scheduleStep_def)
            by metis

          \<comment> \<open>there must be a fireable transition for the schedule state of st2\<close>
          then have "\<exists> t. t \<in> {s. s |\<subseteq>| (ready st2) \<and> s \<in> (dom (nextRel sys))}"
            using scheduleStep_def by auto

          \<comment> \<open>this implies that the set of fireable transitions for st2 must be non-empty\<close>
          from this card_0_eq fin have "card {s. s |\<subseteq>| (ready st2) \<and> s \<in> (dom (nextRel sys))} > 0"
            by auto

          \<comment> \<open>this is a contradiction since it was assumed that there is no fireable transitions for st2\<close>
          from this a113 show False by auto
        qed
      qed
    qed

  \<comment> \<open>wf_SystemState_ReadySub\<close>

    have rs1: "wf_SystemState_ReadySub sys m st1"
      using wf_SystemState_def wf_st1 by auto

    from this a1 a3 a4 have wf_SystemState_ReadySub_st2: "wf_SystemState_ReadySub sys m st2" 
      apply (auto simp add: wf_SystemState_ReadySub_def mkSystemState_def)
    proof -
      fix x y
      assume r1subRIDS: "ready st1 |\<subseteq>| modelReadyIds m"
      assume rUpdate: "ready' = ready st1 |-| choice |\<union>| y"
      assume newSt2: "st2 = \<lparr>systemTasks = systemTasks st1, 
                             systemChs = systemChs st1, 
                             ready = ready st1 |-| choice |\<union>| y, 
                             previousSystemTasks = systemTasks st1, 
                             previousSystemChs = systemChs st1\<rparr>"
      assume choiceInR1: "choice |\<subseteq>| ready st1"
      assume yMove: "nextRel sys choice = Some y"
      assume xInY: "x |\<in>| y"

      \<comment> \<open>ready st1 minus the in places of choice is a subset of the model Ready Ids\<close>
      have "ready st1 |-| choice |\<subseteq>| modelReadyIds m"
        using r1subRIDS by auto 

      \<comment> \<open>the set of out places of choice are a subset of the model rids\<close>
      from wf_sys have "y |\<subseteq>| modelReadyIds m"
        apply (simp add: wf_System_def wf_System_NextRel_def wf_System_NextRel_RanUnion_def)
        by (meson UnI2 ranI yMove)

      \<comment> \<open>all out places of choice are in the NextRel are model rids\<close>
      thus "x |\<in>| modelReadyIds m"
        using xInY by auto
    qed
        
  show ?thesis
    apply (simp add: wf_SystemState_def)
    by (simp add: wf_taskStates_st2 wf_SystemState_systemTasks_dom_st2 wf_chState' 
                  wf_SystemState_NoDeadlock_st2 reachable_st2 wf_SystemState_ReadySub_st2)
qed

lemma multiStep_preserves_wellformedness: 
     "\<lbrakk>(systemStep sys)\<^sup>*\<^sup>* st1 st2; 
        wf_Model m;
        wf_System sys m;
        nextRel_Assumptions sys m;
        wf_SystemState m sys st1\<rbrakk> \<Longrightarrow> wf_SystemState m sys st2"
  apply (induction rule: rtranclp_induct)
  using systemStep_preserves_wellformedness by (auto+)

lemma systemReach_yields_wellformedness: 
  assumes model_wf: "wf_Model m"
     and sys_wf: "wf_System sys m"
     and reach: "systemReach sys st"
     and nextAssms: "nextRel_Assumptions sys m"
     and initState_wf: "wf_SystemState m sys (initSystemState sys)"
   shows "wf_SystemState m sys st"
proof - 
  from reach have 
    multiStep: "((systemStep sys)\<^sup>*\<^sup>* (initSystemState sys) st)" 
    by (simp add: systemReach_def)
  from sys_wf initState_wf multiStep nextAssms show "wf_SystemState m sys st"
    using multiStep_preserves_wellformedness
    using model_wf by auto 
qed

end