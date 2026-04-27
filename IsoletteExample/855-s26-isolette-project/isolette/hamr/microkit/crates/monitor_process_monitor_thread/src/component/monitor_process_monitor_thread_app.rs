// This file will not be overwritten if HAMR codegen is rerun

use data::{Isolette_Data_Model::On_Off, hamr::SchedState, *};
use crate::bridge::monitor_process_monitor_thread_api::*;
use vstd::prelude::*;

verus! {

  pub struct monitor_process_monitor_thread {
    frame_period: i32,
    last_index: u32,
    prev_user_ch: hamr::ScheduleChannels,
    next_user_ch: hamr::ScheduleChannels,
    // PLACEHOLDER MARKER STATE VARS
  }

  impl monitor_process_monitor_thread {
    pub fn new() -> Self
    {
      Self {
        frame_period: 0,
        last_index: u32::MAX,
        prev_user_ch: [0; hamr::hamr_ScheduleChannels_DIM_0],
        next_user_ch: [0; hamr::hamr_ScheduleChannels_DIM_0],
        // PLACEHOLDER MARKER STATE VAR INIT
      }
    }

    pub fn initialize<API: monitor_process_monitor_thread_Put_Api> (
      &mut self,
      api: &mut monitor_process_monitor_thread_Application_Api<API>)
      ensures
        // PLACEHOLDER MARKER INITIALIZATION ENSURES
    {
      log_info("initialize entrypoint invoked");
    }

    pub fn timeTriggered<API: monitor_process_monitor_thread_Full_Api> (
      &mut self,
      api: &mut monitor_process_monitor_thread_Application_Api<API>)
      requires
        // PLACEHOLDER MARKER TIME TRIGGERED REQUIRES
      ensures
        // PLACEHOLDER MARKER TIME TRIGGERED ENSURES
    {
      self.no_verus(api);
    }

    pub fn notify(
      &mut self,
      channel: microkit_channel)
    {
      // this method is called when the monitor does not handle the passed in channel
      match channel {
        _ => {
          log_warn_channel(channel)
        }
      }
    }

    

    #[verifier::external_body]
    pub fn no_verus <API: monitor_process_monitor_thread_Full_Api>(
      &mut self,
      api: &mut monitor_process_monitor_thread_Application_Api<API>) {

      let state = api.get_sched_state();
      let schedule = api.get_sched_schedule();

      if self.last_index == u32::MAX {
        log::info!("Channel Assignments");
        log::info!("  0 - pad");
        log::info!("  2 - producer_p_p1_producer_MON");
        log::info!("  3 - producer_p_p2_producer_MON");
        log::info!("  4 - consumer_p_p_consumer_MON");
        log::info!("  5 - consumer_p_s_consumer_MON");
        log::info!("  6 - monitor_process_monitor_thread_MON\n");

        let n = schedule.num_timeslices as usize;

        log::info!("Schedule ({} timeslices):", n);
        for i in 0..n {
          let ch: u32 = schedule.timeslice_ch[i];
          let ns: u64 = schedule.timeslices[i];
          let user: bool = schedule.is_user_partition[i];
          log::info!("  [{}] ch={}, duration={}ns, user={}", i, ch, ns, user);
        }

        buildUserChannelTables(
          &schedule, &mut self.prev_user_ch, &mut self.next_user_ch);
      }

      if state.current_timeslice <= self.last_index {
        log::info!("################");
        log::info!("# FRAME PERIOD {}", self.frame_period);
        log::info!("################");

        self.frame_period = self.frame_period + 1;
      }

      //log::info!("Schedule State: Post {:?}, Pre {:?} (index {:?})", state.last_yielded_ch, state.next_dispatch_ch, state.current_timeslice);
      log::info!("Schedule State: Index {:?}", state.current_timeslice);

      let idx = state.current_timeslice as usize;
      if self.last_index == u32::MAX {
        log::info!("First compute phase, check initialization guarantees");

        log::info!("Pre Channel: {:?}", self.next_user_ch[idx]);
      } else {
        log::info!("Post Channel: {:?}", self.prev_user_ch[idx]);
        log::info!("Pre Channel: {:?}", self.next_user_ch[idx]);
      }
      /*
      if let Some(v) = api.get_producer_p_p1_producer_write_port() {
        log::info!("Received {:?} from producer_p_p1", v);
      }
      if let Some(v) = api.get_producer_p_p2_producer_write_port() {
        log::info!("Received {:?} from producer_p_p2", v);
      }
      */

      let mri_mri_displayed_temp = api.get_mri_mri_displayed_temp();
      let mri_mri_regulator_status = api.get_mri_mri_regulator_status();
      let mhs_mhs_heat_control = api.get_mhs_mhs_heat_control();
      let mmi_mmi_monitor_status = api.get_mmi_mmi_monitor_status();
      let ma_ma_alarm_control = api.get_ma_ma_alarm_control();
      let oip_oit_lower_desired_tempWstatus = api.get_oip_oit_lower_desired_tempWstatus();
      let oip_oit_upper_desired_tempWstatus = api.get_oip_oit_upper_desired_tempWstatus();
      let oip_oit_lower_alarm_tempWstatus = api.get_oip_oit_lower_alarm_tempWstatus();
      let oip_oit_upper_alarm_tempWstatus = api.get_oip_oit_upper_alarm_tempWstatus();
      let cpi_thermostat_current_tempWstatus = api.get_cpi_thermostat_current_tempWstatus();
      let mri_mri_upper_desired_temp = api.get_mri_mri_upper_desired_temp();
      let mri_mri_lower_desired_temp = api.get_mri_mri_lower_desired_temp();
      let mri_mri_interface_failure = api.get_mri_mri_interface_failure();
      let mrm_mrm_regulator_mode = api.get_mrm_mrm_regulator_mode();
      let drf_drf_internal_failure = api.get_drf_drf_internal_failure();
      let mmi_mmi_upper_alarm_temp = api.get_mmi_mmi_upper_alarm_temp();
      let mmi_mmi_lower_alarm_temp = api.get_mmi_mmi_lower_alarm_temp();
      let mmi_mmi_interface_failure = api.get_mmi_mmi_interface_failure();
      let mmm_mmm_monitor_mode = api.get_mmm_mmm_monitor_mode();
      let dmf_dmf_internal_failure = api.get_dmf_dmf_internal_failure();

      if self.prev_user_ch[idx] == 7 { // Following Manage Regulator Interface
        if sysProp_NormalDisplayTemp(mrm_mrm_regulator_mode, mri_mri_displayed_temp, cpi_thermostat_current_tempWstatus) {
          log_info("[REGULATOR] sysProp_NormalDisplayTemp [PASSING]");
        } else {
          log_info("[REGULATOR] sysProp_NormalDisplayTemp [FAILED]");
        }
      }

      if self.prev_user_ch[idx] == 9 { // Manage Heat Source
        if sysProp_NormalModeHeatOnn(mrm_mrm_regulator_mode, cpi_thermostat_current_tempWstatus, oip_oit_lower_desired_tempWstatus, oip_oit_upper_desired_tempWstatus, drf_drf_internal_failure, mhs_mhs_heat_control) {
          log_info("[REGULATOR] sysProp_NormalModeHeatOnn [PASSING]");
        } else {
          log_info("[REGULATOR] sysProp_NormalModeHeatOnn [FAILED]");
        }

        if sysProp_NormalModeHeatOff(mrm_mrm_regulator_mode, cpi_thermostat_current_tempWstatus, oip_oit_lower_desired_tempWstatus, oip_oit_upper_desired_tempWstatus, drf_drf_internal_failure, mhs_mhs_heat_control) {
          log_info("[REGULATOR] sysProp_NormalModeHeatOff [PASSING]");
        } else {
          log_info("[REGULATOR] sysProp_NormalModeHeatOff [FAILED]");
        }

        if sysProp_InitModeHeatOff(mrm_mrm_regulator_mode, mhs_mhs_heat_control) {
          log_info("[REGULATOR] sysProp_InitModeHeatOff [PASSING]");
        } else {
          log_info("[REGULATOR] sysProp_InitModeHeatOff [FAILED]");
        }

        if sysProp_InvalidCTNormalModeHeatOff(cpi_thermostat_current_tempWstatus, mrm_mrm_regulator_mode, mhs_mhs_heat_control) {
          log_info("[REGULATOR] sysProp_InvalidCTNormalModeHeatOff [PASSING]");
        } else {
          log_info("[REGULATOR] sysProp_InvalidCTNormalModeHeatOff [FAILED]");
        }

        if sysProp_InvalidUDTNormalModeHeatOff(oip_oit_upper_desired_tempWstatus, mrm_mrm_regulator_mode, mhs_mhs_heat_control) {
          log_info("[REGULATOR] sysProp_InvalidUDTNormalModeHeatOff [PASSING]");
        } else {
          log_info("[REGULATOR] sysProp_InvalidUDTNormalModeHeatOff [FAILED]");
        }

        if sysProp_InvalidLDTNormalModeHeatOff(oip_oit_lower_desired_tempWstatus, mrm_mrm_regulator_mode, mhs_mhs_heat_control) {
          log_info("[REGULATOR] sysProp_InvalidLDTNormalModeHeatOff [PASSING]");
        } else {
          log_info("[REGULATOR] sysProp_InvalidLDTNormalModeHeatOff [FAILED]");
        }

        if sysProp_InteralFailureNormalModeHeatOff(drf_drf_internal_failure, mrm_mrm_regulator_mode, mhs_mhs_heat_control) {
          log_info("[REGULATOR] sysProp_InteralFailureNormalModeHeatOff [PASSING]");
        } else {
          log_info("[REGULATOR] sysProp_InteralFailureNormalModeHeatOff [FAILED]");
        }
      }

      self.last_index = state.current_timeslice;
    }
    
  }

  #[verifier::external_body]
  pub fn helper_RegulatorInputErrorCondition( lowerDesiredTempWStatus: Isolette_Data_Model::TempWstatus_i,
                                              upperDesiredTempWStatus: Isolette_Data_Model::TempWstatus_i,
                                              currentTempWStatus: Isolette_Data_Model::TempWstatus_i
                                            ) -> bool {

    return lowerDesiredTempWStatus.status == Isolette_Data_Model::ValueStatus::Invalid 
            || upperDesiredTempWStatus.status == Isolette_Data_Model::ValueStatus::Invalid
            || currentTempWStatus.status == Isolette_Data_Model::ValueStatus::Invalid
  }

  #[verifier::external_body]
  pub fn helper_RegulatorInternalFailureCondition(internalFailure: Isolette_Data_Model::Failure_Flag_i) -> bool {
    return internalFailure.flag
  }

  #[verifier::external_body]
  pub fn helper_RegulatorErrorCondition(lowerDesiredTempWStatus: Isolette_Data_Model::TempWstatus_i,
                                        upperDesiredTempWStatus: Isolette_Data_Model::TempWstatus_i,
                                        currentTempWStatus: Isolette_Data_Model::TempWstatus_i,
                                        internalFailure: Isolette_Data_Model::Failure_Flag_i
                                      ) -> bool {
    return (helper_RegulatorInputErrorCondition(lowerDesiredTempWStatus, upperDesiredTempWStatus, currentTempWStatus)
      || helper_RegulatorInternalFailureCondition(internalFailure))
  }

  //----------------------------------------------
  //  Property:  CT < LDT implies Heat-Control ON
  //    [high-level]
  //      In Normal mode, and in the absence of error-triggering inputs,
  //      If current temp is less than lower desired, then heat control shall be ON
  //----------------------------------------------
  #[verifier::external_body]
  pub fn sysProp_NormalModeHeatOnn( Regulator_ModeIN: Isolette_Data_Model::Regulator_Mode,
                                    currentTempWStatusIN: Isolette_Data_Model::TempWstatus_i,
                                    lowerDesiredTempWStatusIN: Isolette_Data_Model::TempWstatus_i,
                                    upperDesiredTempWStatusIN: Isolette_Data_Model::TempWstatus_i,
                                    internalFailureIN: Isolette_Data_Model::Failure_Flag_i,
                                    heat_controlOut: Isolette_Data_Model::On_Off
                                  ) -> bool{
    return !(
              !(helper_RegulatorErrorCondition(lowerDesiredTempWStatusIN, upperDesiredTempWStatusIN, currentTempWStatusIN, internalFailureIN))
              && Regulator_ModeIN == Isolette_Data_Model::Regulator_Mode::Normal_Regulator_Mode
              && currentTempWStatusIN.degrees < lowerDesiredTempWStatusIN.degrees
            ) 
            ||
            (
              heat_controlOut == Isolette_Data_Model::On_Off::Onn
            );
  }
  
  //----------------------------------------------
  //  Property:  CT > UDT implies Heat-Control Off
  //    [high-level]
  //      In Normal mode, and in the absence of error-triggering inputs,
  //      If current temp is greater than upper desired, then heat control shall be OFF
  //----------------------------------------------
  #[verifier::external_body]
  pub fn sysProp_NormalModeHeatOff( Regulator_ModeIN: Isolette_Data_Model::Regulator_Mode,
                                    currentTempWStatusIN: Isolette_Data_Model::TempWstatus_i,
                                    lowerDesiredTempWStatusIN: Isolette_Data_Model::TempWstatus_i,
                                    upperDesiredTempWStatusIN: Isolette_Data_Model::TempWstatus_i,
                                    internalFailureIN: Isolette_Data_Model::Failure_Flag_i,
                                    heat_controlOut: Isolette_Data_Model::On_Off
                                  ) -> bool{
    return !(
              !(helper_RegulatorErrorCondition(lowerDesiredTempWStatusIN, upperDesiredTempWStatusIN, currentTempWStatusIN, internalFailureIN))
              && Regulator_ModeIN == Isolette_Data_Model::Regulator_Mode::Normal_Regulator_Mode
              && currentTempWStatusIN.degrees > upperDesiredTempWStatusIN.degrees
            ) 
            ||
            (
              heat_controlOut == Isolette_Data_Model::On_Off::Off
            );
  }

  //----------------------------------------------
  //  Property:  In the initialization mode, the heat control should be set to off
  //    [high-level]
  //      In Initialization mode
  //      heat control shall be OFF
  //----------------------------------------------
  #[verifier::external_body]
  pub fn sysProp_InitModeHeatOff( Regulator_ModeIN: Isolette_Data_Model::Regulator_Mode,
                                  heat_controlOut: Isolette_Data_Model::On_Off
                                ) -> bool{
    return !(
              Regulator_ModeIN == Isolette_Data_Model::Regulator_Mode::Init_Regulator_Mode
            ) 
            ||
            (
              heat_controlOut == Isolette_Data_Model::On_Off::Off
            );
  }

  //---------------------------------------------------
  // Error Situations
  //   - shift to Failed Mode
  //   - heat control off
  //---------------------------------------------------
  #[verifier::external_body]
  pub fn sysProp_InvalidCTNormalModeHeatOff(currentTempWStatusIN: Isolette_Data_Model::TempWstatus_i,
                                            Regulator_ModeIn: Isolette_Data_Model::Regulator_Mode,
                                            heat_controlOut: Isolette_Data_Model::On_Off,
                                           ) -> bool {
    return !(
      currentTempWStatusIN.status == Isolette_Data_Model::ValueStatus::Invalid
      && Regulator_ModeIn == Isolette_Data_Model::Regulator_Mode::Normal_Regulator_Mode
    )    
    ||
    (
      heat_controlOut == Isolette_Data_Model::On_Off::Off
    )                            
  }

  #[verifier::external_body]
  pub fn sysProp_InvalidUDTNormalModeHeatOff(upperDesiredTempWStatusIN: Isolette_Data_Model::TempWstatus_i,
                                             Regulator_ModeIn: Isolette_Data_Model::Regulator_Mode,
                                             heat_controlOut: Isolette_Data_Model::On_Off,
                                            ) -> bool {
    return !(
      upperDesiredTempWStatusIN.status == Isolette_Data_Model::ValueStatus::Invalid
      && Regulator_ModeIn == Isolette_Data_Model::Regulator_Mode::Normal_Regulator_Mode
    )    
    ||
    (
      heat_controlOut == Isolette_Data_Model::On_Off::Off
    )                            
  }

  #[verifier::external_body]
  pub fn sysProp_InvalidLDTNormalModeHeatOff(lowerDesiredTempWStatusIN: Isolette_Data_Model::TempWstatus_i,
                                             Regulator_ModeIn: Isolette_Data_Model::Regulator_Mode,
                                             heat_controlOut: Isolette_Data_Model::On_Off,
                                            ) -> bool {
    return !(
      lowerDesiredTempWStatusIN.status == Isolette_Data_Model::ValueStatus::Invalid
      && Regulator_ModeIn == Isolette_Data_Model::Regulator_Mode::Normal_Regulator_Mode
    )    
    ||
    (
      heat_controlOut == Isolette_Data_Model::On_Off::Off
    )                            
  }

  #[verifier::external_body]
  pub fn sysProp_InteralFailureNormalModeHeatOff(internalFailure: Isolette_Data_Model::Failure_Flag_i,
                                                 Regulator_ModeIn: Isolette_Data_Model::Regulator_Mode,
                                                 heat_controlOut: Isolette_Data_Model::On_Off,
                                                ) -> bool {
    return !(
      helper_RegulatorInternalFailureCondition(internalFailure)
      && Regulator_ModeIn == Isolette_Data_Model::Regulator_Mode::Normal_Regulator_Mode
    )    
    ||
    (
      heat_controlOut == Isolette_Data_Model::On_Off::Off
    )                            
  }

  // ===========================  Display Temperature Properties ========================

  #[verifier::external_body]
  pub fn sysProp_NormalDisplayTemp(Regulator_ModeIN: Isolette_Data_Model::Regulator_Mode,
                                   display_temperatureOUT: Isolette_Data_Model::Temp_i,
                                   currentTempWStatusIN: Isolette_Data_Model::TempWstatus_i
                                  ) -> bool {

    return !(
      Regulator_ModeIN == Isolette_Data_Model::Regulator_Mode::Normal_Regulator_Mode
    ) 
    || 
    (
      display_temperatureOUT.degrees == currentTempWStatusIN.degrees
    );
  }

  //====================================================================
  //  Mode Transition Properties
  //====================================================================

  // Are we allow to use a "sudo-admim-component" that snapshots the enitre state of the system at the start

  /*
  pub fn sysProp_NormalToNormalMode(Regulator_ModeIN: Isolette_Data_Model::Regulator_Mode,
                                    lowerDesiredTempWStatus: Isolette_Data_Model::TempWstatus_i,
                                    upperDesiredTempWStatus: Isolette_Data_Model::TempWstatus_i,
                                    currentTempWStatus: Isolette_Data_Model::TempWstatus_i,
                                    internalFailure: Isolette_Data_Model::Failure_Flag_i) -> bool = {
    val triggerCondition: B = (
      & inputs_container.mode == Regulator_Mode.Normal_Regulator_Mode)

    val desiredCondition: B = (outputs_container.mode == Regulator_Mode.Normal_Regulator_Mode)

    bookKeep(triggerCondition, desiredCondition)

    return !(
      !helper_RegulatorErrorCondition(inputs_container)
    )
    ||
    (

    )
  }*/

  #[verifier::external_body]
  pub fn buildUserChannelTables(
    sched: &hamr::Schedule,
    prev: &mut hamr::ScheduleChannels,
    next: &mut hamr::ScheduleChannels)
  {
    let n = sched.num_timeslices as usize;
    for i in 0..n {
      let mut found_prev = false;
      let mut found_next = false;
      for offset in 1..n {
        if !found_prev {
          let backward = (i + n - offset) % n;
          if sched.is_user_partition[backward] {
            prev[i] = sched.timeslice_ch[backward];
            found_prev = true;
          }
        }
        if !found_next {
          let forward = (i + offset) % n;
          if sched.is_user_partition[forward] {
            next[i] = sched.timeslice_ch[forward];
            found_next = true;
          }
        }
        if found_prev && found_next {
          break;
        }
      }
    }
  }


  #[verifier::external_body]
  pub fn log_info(msg: &str)
  {
    log::info!("{0}", msg);
  }

  #[verifier::external_body]
  pub fn log_slot(msg: SchedState)
  {
    log::info!("Last Dispatched = {}", msg.last_yielded_ch);
    log::info!("Next Dispatched = {}", msg.next_dispatch_ch);
  }

  #[verifier::external_body]
  pub fn log_warn_channel(channel: u32)
  {
    log::warn!("Unexpected channel: {0}", channel);
  }

  // PLACEHOLDER MARKER GUMBO METHODS

}
