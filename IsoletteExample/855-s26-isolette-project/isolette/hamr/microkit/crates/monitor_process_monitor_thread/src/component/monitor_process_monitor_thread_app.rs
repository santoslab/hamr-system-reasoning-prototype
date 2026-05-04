// This file will not be overwritten if HAMR codegen is rerun

use data::{Isolette_Data_Model::On_Off, hamr::SchedState, *};
use crate::bridge::{monitor_process_monitor_thread_api::*};
use vstd::prelude::*;

verus! {

  pub struct monitor_process_monitor_thread {
    frame_period: i32,
    last_index: u32,
    prev_user_ch: hamr::ScheduleChannels,
    next_user_ch: hamr::ScheduleChannels,
    // PLACEHOLDER MARKER STATE VARS
  }

  #[repr(C)]
  #[derive(Debug, Clone, Copy, PartialEq, Eq)]
  pub struct PreState_thermostat_rt_mhs_mhs {
    pub In_lastCmd: Isolette_Data_Model::On_Off,
    pub api_current_tempWstatus: Isolette_Data_Model::TempWstatus_i,
    pub api_lower_desired_temp: Isolette_Data_Model::Temp_i,
    pub api_upper_desired_temp: Isolette_Data_Model::Temp_i,
    pub api_regulator_mode: Isolette_Data_Model::Regulator_Mode,
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

      //channels
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

      //local variables
      
      /*
        --------------------------------------------------------------
        ASSOCIATED PETRI NET WALK
        --------------------------------------------------------------
          {START_Assert} 

          --SPLIT--> 
          {START_OI_Assert, START_TS_Assert} 

          --TS--> 
          {START_OI_Assert, END_TS_Assert} 

          --OI--> 
          {END_OI_Assert, END_TS_Assert}

          --JOIN--> 
          {Post_TS_OI_Assert} 

          --SPLIT--> 
          {START_Regulator_Assert, START_Monitor_Assert}

          --DMF--> 
          {START_Regulator_Assert, Post_DMF_Assert}

          --MMI--> 
          {START_Regulator_Assert, Post_MMI_Assert}
          
          --MMM--> 
          {START_Regulator_Assert, Post_MMM_Assert}

          --MA--> 
          {START_Regulator_Assert, END_Monitor_Assert}

          --DRF--> 
          {Post_DRF_Assert, END_Monitor_Assert}

          --MRI--> 
          {Post_MRI_Assert, END_Monitor_Assert}

          --MRM--> 
          {Post_MRM_Assert, END_Monitor_Assert}

          --MHS--> 
          {END_Regulator_Assert, END_Monitor_Assert}

          --JOIN--> 
          {START_HS_Assert}

          --HS--> 
          {END_Assert}
        
        --------------------------------------------------------------
        COLLAPSED WALK
        --------------------------------------------------------------
          {START_Assert, START_OI_Assert, START_TS_Assert} 

          --TS--> 
          {START_OI_Assert, END_TS_Assert} 

          --OI--> 
          {END_OI_Assert, END_TS_Assert, Post_TS_OI_Assert, START_Regulator_Assert, START_Monitor_Assert}

          --DMF--> 
          {START_Regulator_Assert, Post_DMF_Assert}

          --MMI--> 
          {START_Regulator_Assert, Post_MMI_Assert}
          
          --MMM--> 
          {START_Regulator_Assert, Post_MMM_Assert}

          --MA--> 
          {START_Regulator_Assert, END_Monitor_Assert}

          --DRF--> 
          {Post_DRF_Assert, END_Monitor_Assert}

          --MRI--> 
          {Post_MRI_Assert, END_Monitor_Assert}

          --MRM--> 
          {Post_MRM_Assert, END_Monitor_Assert}

          --MHS--> 
          {END_Regulator_Assert, END_Monitor_Assert, START_HS_Assert}

          --HS--> 
          {END_Assert}
      */


      match self.prev_user_ch[idx] {
        2 => { //Temp Sensor

          if (END_TS_Assert()) {
            log_info("[Post TEMP SENSOR] END_TS_Assert PASSED");
          } else {
            log_info("[Post TEMP SENSOR] END_TS_Assert FAILED");
          }
          
          if(START_OI_Assert()) {
            log_info("[Post TEMP SENSOR] START_OI_Assert PASSED");
          } else {
            log_info("[Post TEMP SENSOR] START_OI_Assert FAILED");
          }
        },
        3 => { // Operator Interface
          if (END_OI_Assert(oip_oit_lower_alarm_tempWstatus, oip_oit_upper_alarm_tempWstatus, oip_oit_lower_desired_tempWstatus, oip_oit_upper_desired_tempWstatus)) {
            log_info("[Post Operator Interface] END_OI_Assert PASSED");
          } else {
            log_info("[Post Operator Interface] END_OI_Assert FAILED");
          }
          
          if(END_TS_Assert()) {
            log_info("[Post Operator Interface] END_TS_Assert PASSED");
          } else {
            log_info("[Post Operator Interface] END_TS_Assert FAILED");
          }
          
          if(Post_TS_OI_Assert()) {
            log_info("[Post Operator Interface] Post_TS_OI_Assert PASSED");
          } else {
            log_info("[Post Operator Interface] Post_TS_OI_Assert FAILED");
          }

          if (START_Regulator_Assert(oip_oit_lower_desired_tempWstatus, oip_oit_upper_desired_tempWstatus)) {
            log_info("[Post Operator Interface] START_Regulator_Assert PASSED");
          } else {
            log_info("[Post Operator Interface] START_Regulator_Assert FAILED");
          }
          
          if(START_Monitor_Assert(oip_oit_lower_alarm_tempWstatus, oip_oit_upper_alarm_tempWstatus)) {
            log_info("[Post Operator Interface] START_Monitor_Assert PASSED");
          } else {
            log_info("[Post Operator Interface] START_Monitor_Assert FAILED");
          }
        },
        4 => { // Detect Monitor Failure
          if (START_Regulator_Assert(oip_oit_lower_desired_tempWstatus, oip_oit_upper_desired_tempWstatus)) {
            log_info("[Post DMF] START_Regulator_Assert PASSED");
          } else {
            log_info("[Post DMF] START_Regulator_Assert FAILED");
          }
          
          if (Post_DMF_Assert(oip_oit_lower_desired_tempWstatus, oip_oit_upper_desired_tempWstatus)) {
            log_info("[Post DMF] Post_DMF_Assert PASSED");
          } else {
            log_info("[Post DMF] Post_DMF_Assert FAILED");
          }
        },
        5 => { // Manage Monitor Interface
          if (START_Regulator_Assert(oip_oit_lower_desired_tempWstatus, oip_oit_upper_desired_tempWstatus)) {
            log_info("[Post MMI] START_Regulator_Assert PASSED");
          } else {
            log_info("[Post MMI] START_Regulator_Assert FAILED");
          }
          
          if (Post_MMI_Assert(oip_oit_lower_alarm_tempWstatus, oip_oit_upper_alarm_tempWstatus, mmi_mmi_lower_alarm_temp, mmi_mmi_upper_alarm_temp, mmi_mmi_interface_failure)) {
            log_info("[Post MMI] Post_MMI_Assert PASSED");
          } else {
            log_info("[Post MMI] Post_MMI_Assert FAILED");
          }
        },
        6 => { // Manage Monitor Mode
          if (START_Regulator_Assert(oip_oit_lower_desired_tempWstatus, oip_oit_upper_desired_tempWstatus)) {
            log_info("[Post MMM] START_Regulator_Assert PASSED");
          } else {
            log_info("[Post MMM] START_Regulator_Assert FAILED");
          }
          
          if (Post_MMM_Assert(oip_oit_lower_alarm_tempWstatus, oip_oit_upper_alarm_tempWstatus, mmi_mmi_lower_alarm_temp, mmi_mmi_upper_alarm_temp, mmi_mmi_interface_failure)) {
            log_info("[Post MMM] Post_MMM_Assert PASSED");
          } else {
            log_info("[Post MMM] Post_MMM_Assert FAILED");
          }
        },
        7 => { // Manage Alarm
          if (START_Regulator_Assert(oip_oit_lower_desired_tempWstatus, oip_oit_upper_desired_tempWstatus)) {
            log_info("[Post MA] START_Regulator_Assert PASSED");
          } else {
            log_info("[Post MA] START_Regulator_Assert FAILED");
          }
          
          if (END_Monitor_Assert(oip_oit_lower_alarm_tempWstatus, oip_oit_upper_alarm_tempWstatus, cpi_thermostat_current_tempWstatus, mmm_mmm_monitor_mode, mmi_mmi_interface_failure, ma_ma_alarm_control)) {
            log_info("[Post MA] END_Monitor_Assert PASSED");
          } else {
            log_info("[Post MA] END_Monitor_Assert FAILED");
          }
        },
        8 => { // Detect Regulator Failure
          if (Post_DRF_Assert(oip_oit_lower_desired_tempWstatus, oip_oit_upper_desired_tempWstatus)) {
            log_info("[Post DRF] Post_DRF_Assert PASSED");
          } else {
            log_info("[Post DRF] Post_DRF_Assert FAILED");
          }
          
          if (END_Monitor_Assert(oip_oit_lower_alarm_tempWstatus, oip_oit_upper_alarm_tempWstatus, cpi_thermostat_current_tempWstatus, mmm_mmm_monitor_mode, mmi_mmi_interface_failure, ma_ma_alarm_control)) {
            log_info("[Post DRF] END_Monitor_Assert PASSED");
          } else {
            log_info("[Post DRF] END_Monitor_Assert FAILED");
          }
        },
        9 => { // Manage Regulator Interface
          if (Post_MRI_Assert(oip_oit_lower_desired_tempWstatus, oip_oit_upper_desired_tempWstatus, mri_mri_lower_desired_temp, mri_mri_upper_desired_temp, mri_mri_interface_failure)) {
            log_info("[Post MRI] Post_MRI_Assert PASSED");
          } else {
            log_info("[Post MRI] Post_MRI_Assert FAILED");
          }
          
          if (END_Monitor_Assert(oip_oit_lower_alarm_tempWstatus, oip_oit_upper_alarm_tempWstatus, cpi_thermostat_current_tempWstatus, mmm_mmm_monitor_mode, mmi_mmi_interface_failure, ma_ma_alarm_control)) {
            log_info("[Post MRI] END_Monitor_Assert PASSED");
          } else {
            log_info("[Post MRI] END_Monitor_Assert FAILED");
          }
        },
        10 => { // Manage Regulator Mode
          if (Post_MRM_Assert(oip_oit_lower_desired_tempWstatus, oip_oit_upper_desired_tempWstatus, mri_mri_lower_desired_temp, mri_mri_upper_desired_temp, mri_mri_interface_failure)) {
            log_info("[Post MRI] Post_MRI_Assert PASSED");
          } else {
            log_info("[Post MRI] Post_MRI_Assert FAILED");
          }
          
          if (END_Monitor_Assert(oip_oit_lower_alarm_tempWstatus, oip_oit_upper_alarm_tempWstatus, cpi_thermostat_current_tempWstatus, mmm_mmm_monitor_mode, mmi_mmi_interface_failure, ma_ma_alarm_control)) {
            log_info("[Post MRI] END_Monitor_Assert PASSED");
          } else {
            log_info("[Post MRI] END_Monitor_Assert FAILED");
          }

          let pre = PreState_thermostat_rt_mhs_mhs {
            In_lastCmd: api.get_mhs_mhs_sv_lastCmd(),
            api_current_tempWstatus: api.get_cpi_thermostat_current_tempWstatus(),
            api_lower_desired_temp: api.get_mri_mri_lower_desired_temp(),
            api_upper_desired_temp: api.get_mri_mri_upper_desired_temp(),
            api_regulator_mode: api.get_mrm_mrm_regulator_mode(),
          };
          log::info!("mhs pre state: {:?}", pre);

        },
        11 => { // Manage Heat Source
          if (END_Regulator_Assert(mrm_mrm_regulator_mode, cpi_thermostat_current_tempWstatus, oip_oit_lower_desired_tempWstatus, oip_oit_upper_desired_tempWstatus, drf_drf_internal_failure, mhs_mhs_heat_control)) {
            log_info("[Post MHS] END_Regulator_Assert PASSED");
          } else {
            log_info("[Post MHS] END_Regulator_Assert FAILED");
          }
          
          if (END_Monitor_Assert(oip_oit_lower_alarm_tempWstatus, oip_oit_upper_alarm_tempWstatus, cpi_thermostat_current_tempWstatus, mmm_mmm_monitor_mode, mmi_mmi_interface_failure, ma_ma_alarm_control)) {
            log_info("[Post MHS] END_Monitor_Assert PASSED");
          } else {
            log_info("[Post MHS] END_Monitor_Assert FAILED");
          }

          if (START_HS_Assert()) {
            log_info("[Post MHS] START_HS_Assert PASSED");
          } else {
            log_info("[Post MHS] START_HS_Assert FAILED");
          }
        },
        12 => { // Heat Source
          if(END_Assert()) {
            log_info("[Post HS] END_Assert PASSED");
          } else {
            log_info("[Post HS] END_Assert FAILED");
          }

          if(START_Assert()) {
            log_info("[Post HS] START_Assert PASSED");
          } else {
            log_info("[Post HS] START_Assert FAILED");
          }

          if(START_OI_Assert()) {
            log_info("[Post HS] START_OI_Assert PASSED");
          } else {
            log_info("[Post HS] START_OI_Assert FAILED");
          }

          if(START_TS_Assert()) {
            log_info("[Post HS] START_TS_Assert PASSED");
          } else {
            log_info("[Post HS] START_TS_Assert FAILED");
          }
        },
        _ => log_info("SHCEDULE ERROR")
      }


      self.last_index = state.current_timeslice;
    }
    
  }
  
  // =========================== System Assert Functions ===========================


  #[verifier::external_body]
  pub fn START_Assert() -> bool {
    true
  }

  #[verifier::external_body]
  pub fn START_OI_Assert() -> bool {
    true
  }

  #[verifier::external_body]
  pub fn END_OI_Assert(lower_alarm_tempWstatus: Isolette_Data_Model::TempWstatus_i,
                       upper_alarm_tempWStatus: Isolette_Data_Model::TempWstatus_i,
                       lower_desired_tempWstatus: Isolette_Data_Model::TempWstatus_i,
                       upper_desired_tempWstatus: Isolette_Data_Model::TempWstatus_i
                      ) -> bool {
    sysProp_Allowed_LowerAlarmTempWstatus(lower_alarm_tempWstatus)
    && sysProp_Allowed_UpperAlarmTempWstatus(upper_alarm_tempWStatus)
    && sysProp_Allowed_AlarmTempWStatus_Ranges(lower_alarm_tempWstatus, upper_alarm_tempWStatus)
    && sysProp_lower_is_not_higher_than_upper(lower_desired_tempWstatus, upper_desired_tempWstatus)
  }

  #[verifier::external_body]
  pub fn START_TS_Assert() -> bool {
    true
  }

  #[verifier::external_body]
  pub fn END_TS_Assert() -> bool {
    true
  }

  #[verifier::external_body]
  pub fn Post_TS_OI_Assert() -> bool {
    true
  }

  #[verifier::external_body]
  pub fn START_Regulator_Assert(lower_desired_tempWstatus: Isolette_Data_Model::TempWstatus_i,
                                upper_desired_tempWstatus: Isolette_Data_Model::TempWstatus_i) -> bool {
    sysProp_lower_is_not_higher_than_upper(lower_desired_tempWstatus, upper_desired_tempWstatus)
  }

  #[verifier::external_body]
  pub fn Post_DRF_Assert(lower_desired_tempWstatus: Isolette_Data_Model::TempWstatus_i,
                         upper_desired_tempWstatus: Isolette_Data_Model::TempWstatus_i) -> bool {
    sysProp_lower_is_not_higher_than_upper(lower_desired_tempWstatus, upper_desired_tempWstatus)
  }

  #[verifier::external_body]
  pub fn Post_MRI_Assert(lower_desired_tempWstatus: Isolette_Data_Model::TempWstatus_i,
                          upper_desired_tempWstatus: Isolette_Data_Model::TempWstatus_i,
                          lower_desired_temp: Isolette_Data_Model::Temp_i,
                          upper_desired_temp: Isolette_Data_Model::Temp_i,
                          interface_failure: Isolette_Data_Model::Failure_Flag_i) -> bool {
    sysProp_REQ_MRI_7(lower_desired_tempWstatus,  upper_desired_tempWstatus, interface_failure)
    && sysProp_REQ_MRI_8(lower_desired_tempWstatus, upper_desired_tempWstatus, lower_desired_temp, upper_desired_temp, interface_failure)
    && sysProp_lower_is_lower_temp(lower_desired_temp, upper_desired_temp)
  }

  #[verifier::external_body]
  pub fn Post_MRM_Assert(lower_desired_tempWstatus: Isolette_Data_Model::TempWstatus_i,
                          upper_desired_tempWstatus: Isolette_Data_Model::TempWstatus_i,
                          lower_desired_temp: Isolette_Data_Model::Temp_i,
                          upper_desired_temp: Isolette_Data_Model::Temp_i,
                          interface_failure: Isolette_Data_Model::Failure_Flag_i) -> bool {
    sysProp_REQ_MRI_7(lower_desired_tempWstatus,  upper_desired_tempWstatus, interface_failure)
    && sysProp_REQ_MRI_8(lower_desired_tempWstatus, upper_desired_tempWstatus, lower_desired_temp, upper_desired_temp, interface_failure)
    && sysProp_lower_is_lower_temp(lower_desired_temp, upper_desired_temp)
  }

  #[verifier::external_body]
  pub fn END_Regulator_Assert(regulator_mode: Isolette_Data_Model::Regulator_Mode,
                              currentTempWStatus: Isolette_Data_Model::TempWstatus_i,
                              lowerDesiredTempWStatus: Isolette_Data_Model::TempWstatus_i,
                              upperDesiredTempWStatus: Isolette_Data_Model::TempWstatus_i,
                              internalFailure: Isolette_Data_Model::Failure_Flag_i,
                              heat_control: Isolette_Data_Model::On_Off) -> bool {
    sysProp_NormalModeHeatOnn(regulator_mode, currentTempWStatus, lowerDesiredTempWStatus, upperDesiredTempWStatus, internalFailure, heat_control)
  }

  #[verifier::external_body]
  pub fn START_Monitor_Assert(lower_alarm_tempWstatus: Isolette_Data_Model::TempWstatus_i,
                              upper_alarm_tempWStatus: Isolette_Data_Model::TempWstatus_i) -> bool {
    sysProp_Allowed_LowerAlarmTempWstatus(lower_alarm_tempWstatus)
    && sysProp_Allowed_UpperAlarmTempWstatus(upper_alarm_tempWStatus)
    && sysProp_Allowed_AlarmTempWStatus_Ranges(lower_alarm_tempWstatus, upper_alarm_tempWStatus)
  }

  #[verifier::external_body]
  pub fn Post_DMF_Assert(lower_alarm_tempWstatus: Isolette_Data_Model::TempWstatus_i,
                         upper_alarm_tempWStatus: Isolette_Data_Model::TempWstatus_i) -> bool {
    sysProp_Allowed_LowerAlarmTempWstatus(lower_alarm_tempWstatus)
    && sysProp_Allowed_UpperAlarmTempWstatus(upper_alarm_tempWStatus)
    && sysProp_Allowed_AlarmTempWStatus_Ranges(lower_alarm_tempWstatus, upper_alarm_tempWStatus)
  }

  #[verifier::external_body]
  pub fn Post_MMI_Assert(lower_alarm_tempWstatus: Isolette_Data_Model::TempWstatus_i,
                            upper_alarm_tempWstatus: Isolette_Data_Model::TempWstatus_i,
                            lower_alarm_temp: Isolette_Data_Model::Temp_i,
                            upper_alarm_temp: Isolette_Data_Model::Temp_i,
                            interface_failure: Isolette_Data_Model::Failure_Flag_i) -> bool {
    sysProp_REQ_MMI_5(lower_alarm_tempWstatus, upper_alarm_tempWstatus, interface_failure)
    && sysProp_REQ_MMI_6(lower_alarm_tempWstatus, upper_alarm_tempWstatus, lower_alarm_temp, upper_alarm_temp, interface_failure)
    && sysProp_Figure_A_7_Weakened(lower_alarm_temp, upper_alarm_temp)
    && sysProp_Table_A_12_LowerAlarmTemp(lower_alarm_temp)
    && sysProp_Table_A_12_UpperAlarmTemp(upper_alarm_temp)
  }

  #[verifier::external_body]
  pub fn Post_MMM_Assert(lower_alarm_tempWstatus: Isolette_Data_Model::TempWstatus_i,
                            upper_alarm_tempWstatus: Isolette_Data_Model::TempWstatus_i,
                            lower_alarm_temp: Isolette_Data_Model::Temp_i,
                            upper_alarm_temp: Isolette_Data_Model::Temp_i,
                            interface_failure: Isolette_Data_Model::Failure_Flag_i) -> bool {
    sysProp_REQ_MMI_5(lower_alarm_tempWstatus, upper_alarm_tempWstatus, interface_failure)
    && sysProp_REQ_MMI_6(lower_alarm_tempWstatus, upper_alarm_tempWstatus, lower_alarm_temp, upper_alarm_temp, interface_failure)
    && sysProp_Figure_A_7_Weakened(lower_alarm_temp, upper_alarm_temp)
    && sysProp_Table_A_12_LowerAlarmTemp(lower_alarm_temp)
    && sysProp_Table_A_12_UpperAlarmTemp(upper_alarm_temp)
  }

  #[verifier::external_body]
  pub fn END_Monitor_Assert(
                            lower_alarm_tempWstatus: Isolette_Data_Model::TempWstatus_i,
                            upper_alarm_tempWStatus: Isolette_Data_Model::TempWstatus_i,
                            current_tempWstatus: Isolette_Data_Model::TempWstatus_i,
                            monitor_mode: Isolette_Data_Model::Monitor_Mode,
                            interface_failure: Isolette_Data_Model::Failure_Flag_i,
                            alarm_control: Isolette_Data_Model::On_Off
                          ) -> bool {
    sysProp_NormalModeAlarmOn(lower_alarm_tempWstatus, upper_alarm_tempWStatus, current_tempWstatus, monitor_mode, interface_failure, alarm_control)
  }

  #[verifier::external_body]
  pub fn START_HS_Assert () -> bool {
    true
  }

  #[verifier::external_body]
  pub fn END_Assert () -> bool {
    true
  }

  // ===========================  Operator Interface  =======================

    #[verifier::external_body]
    pub fn sysProp_Allowed_LowerAlarmTempWstatus(lower_alarm_tempWstatus: Isolette_Data_Model::TempWstatus_i) -> bool {
      GUMBO_Library::Allowed_LowerAlarmTempWStatus(lower_alarm_tempWstatus)
    }

    #[verifier::external_body]
    pub fn sysProp_Allowed_UpperAlarmTempWstatus(upper_alarm_tempWStatus: Isolette_Data_Model::TempWstatus_i) -> bool {
      GUMBO_Library::Allowed_UpperAlarmTempWStatus(upper_alarm_tempWStatus)
    }

    #[verifier::external_body]   
    pub fn sysProp_Allowed_AlarmTempWStatus_Ranges(lower_alarm_tempWstatus: Isolette_Data_Model::TempWstatus_i,
                                                    upper_alarm_tempWStatus: Isolette_Data_Model::TempWstatus_i) -> bool {
      GUMBO_Library::Allowed_AlarmTempWStatus_Ranges(lower_alarm_tempWstatus, upper_alarm_tempWStatus)
    }
  
  // ===========================  Monitor Properties ========================

  // ===== Helper Functions =====

  #[verifier::external_body]
  pub fn helper_MonitorInputErrorCondition(lowerAlarmTempWStatus: Isolette_Data_Model::TempWstatus_i,
                                           upperAlarmTempWStatus: Isolette_Data_Model::TempWstatus_i,
                                           currentTempWStatus: Isolette_Data_Model::TempWstatus_i) -> bool {
    lowerAlarmTempWStatus.status == Isolette_Data_Model::ValueStatus::Invalid ||
    upperAlarmTempWStatus.status == Isolette_Data_Model::ValueStatus::Invalid ||
    currentTempWStatus.status == Isolette_Data_Model::ValueStatus::Invalid
  }

  #[verifier::external_body]
  pub fn helper_MonitorInternalFailureCondition(internalFailure: Isolette_Data_Model::Failure_Flag_i) -> bool {
    internalFailure.flag
  }

  #[verifier::external_body]
  pub fn helper_MonitorErrorCondition(lowerAlarmTempWStatus: Isolette_Data_Model::TempWstatus_i,
                                      upperAlarmTempWStatus: Isolette_Data_Model::TempWstatus_i,
                                      currentTempWStatus: Isolette_Data_Model::TempWstatus_i,
                                      internalFailure: Isolette_Data_Model::Failure_Flag_i) -> bool {
    helper_MonitorInputErrorCondition(lowerAlarmTempWStatus, upperAlarmTempWStatus, currentTempWStatus) |
    helper_MonitorInternalFailureCondition(internalFailure)
  }

  // ===== Properties Functions =====

  #[verifier::external_body]
  pub fn sysProp_Table_A_12_LowerAlarmTemp(lower_alarm_temp: Isolette_Data_Model::Temp_i) -> bool{
    GUMBO_Library::Allowed_LowerAlarmTemp(lower_alarm_temp.degrees)
  }

  #[verifier::external_body]                
  pub fn sysProp_Table_A_12_UpperAlarmTemp(upper_alarm_temp: Isolette_Data_Model::Temp_i) -> bool {
    GUMBO_Library::Allowed_UpperAlarmTemp(upper_alarm_temp.degrees)
  }

  #[verifier::external_body]
  pub fn sysProp_Figure_A_7_Weakened(lower_alarm_temp: Isolette_Data_Model::Temp_i, 
                                     upper_alarm_temp: Isolette_Data_Model::Temp_i) -> bool {
    lower_alarm_temp.degrees <= upper_alarm_temp.degrees
  }
              

  //derived from REQ_MMI_5
  #[verifier::external_body]
  pub fn sysProp_REQ_MMI_5(lower_alarm_tempWstatus: Isolette_Data_Model::TempWstatus_i,
                            upper_alarm_tempWstatus: Isolette_Data_Model::TempWstatus_i,
                            interface_failure: Isolette_Data_Model::Failure_Flag_i
                          ) -> bool {
                            !(
                              !((upper_alarm_tempWstatus.status == Isolette_Data_Model::ValueStatus::Valid) 
                                && (lower_alarm_tempWstatus.status == Isolette_Data_Model::ValueStatus::Valid))
                            )
                            || 
                            (
                              !interface_failure.flag
                            )
                          }

  //derived from REQ_MMI_6
  #[verifier::external_body]
  pub fn sysProp_REQ_MMI_6(lower_alarm_tempWstatus: Isolette_Data_Model::TempWstatus_i,
                            upper_alarm_tempWstatus: Isolette_Data_Model::TempWstatus_i,
                            lower_alarm_temp: Isolette_Data_Model::Temp_i,
                            upper_alarm_temp: Isolette_Data_Model::Temp_i,
                            interface_failure: Isolette_Data_Model::Failure_Flag_i
                        ) -> bool {
                          !(
                            !interface_failure.flag
                          )
                          || 
                          (
                            lower_alarm_temp.degrees == lower_alarm_tempWstatus.degrees 
                            && upper_alarm_temp.degrees == upper_alarm_tempWstatus.degrees
                          )
                        }
              

  #[verifier::external_body]
  pub fn sysProp_NormalModeAlarmOn(lowerAlarmTempWStatus: Isolette_Data_Model::TempWstatus_i,
                                   upperAlarmTempWStatus: Isolette_Data_Model::TempWstatus_i,
                                   currentTempWStatus: Isolette_Data_Model::TempWstatus_i,
                                   monitor_mode: Isolette_Data_Model::Monitor_Mode,
                                   internalFailure: Isolette_Data_Model::Failure_Flag_i,
                                   alarm_control: Isolette_Data_Model::On_Off) -> bool {

    !(
      !helper_MonitorErrorCondition(lowerAlarmTempWStatus, upperAlarmTempWStatus, currentTempWStatus, internalFailure) &&
      monitor_mode ==Isolette_Data_Model::Monitor_Mode::Normal_Monitor_Mode &&
      (currentTempWStatus.degrees < lowerAlarmTempWStatus.degrees ||
       currentTempWStatus.degrees > upperAlarmTempWStatus.degrees)
    ) 
    || 
    (
      alarm_control == Isolette_Data_Model::On_Off::Onn
    )
  }


  // ===========================  Regulator Properties ========================

  // ===== Helper Functions =====

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

  // ===== Properties Functions =====

  #[verifier::external_body]
  pub fn sysProp_lower_is_not_higher_than_upper(lower_desired_tempWstatus: Isolette_Data_Model::TempWstatus_i,
                                                upper_desired_tempWstatus: Isolette_Data_Model::TempWstatus_i) -> bool {
   lower_desired_tempWstatus.degrees <= upper_desired_tempWstatus.degrees
  }

  #[verifier::external_body]
  pub fn sysProp_lower_is_lower_temp(lower_desired_temp: Isolette_Data_Model::Temp_i,
                                     upper_desired_temp: Isolette_Data_Model::Temp_i) -> bool {
   lower_desired_temp.degrees <= upper_desired_temp.degrees
  }


  //derived from REQ_MRI_7
  #[verifier::external_body]
  pub fn sysProp_REQ_MRI_7( lower_desired_tempWstatus: Isolette_Data_Model::TempWstatus_i,
                            upper_desired_tempWstatus: Isolette_Data_Model::TempWstatus_i,
                            interface_failure: Isolette_Data_Model::Failure_Flag_i
                          ) -> bool {
                            (interface_failure.flag == (!((upper_desired_tempWstatus.status == Isolette_Data_Model::ValueStatus::Valid) 
                                                        && (lower_desired_tempWstatus.status == Isolette_Data_Model::ValueStatus::Valid))))
                          }

  //derived from REQ_MRI_8
  #[verifier::external_body]
  pub fn sysProp_REQ_MRI_8( lower_desired_tempWstatus: Isolette_Data_Model::TempWstatus_i,
                            upper_desired_tempWstatus: Isolette_Data_Model::TempWstatus_i,
                            lower_desired_temp: Isolette_Data_Model::Temp_i,
                            upper_desired_temp: Isolette_Data_Model::Temp_i,
                            interface_failure: Isolette_Data_Model::Failure_Flag_i
                         ) -> bool {
                            !(
                              !interface_failure.flag
                            )
                            || 
                            (
                              lower_desired_temp.degrees == lower_desired_tempWstatus.degrees 
                              && upper_desired_temp.degrees == upper_desired_tempWstatus.degrees
                            )
                         }

  //----------------------------------------------
  //  Property:  CT < LDT implies Heat-Control ON
  //    [high-level]
  //      In Normal mode, and in the absence of error-triggering inputs,
  //      If current temp is less than lower desired, then heat control shall be ON
  //----------------------------------------------
  #[verifier::external_body]
  pub fn sysProp_NormalModeHeatOnn( regulator_mode: Isolette_Data_Model::Regulator_Mode,
                                    currentTempWStatus: Isolette_Data_Model::TempWstatus_i,
                                    lowerDesiredTempWStatus: Isolette_Data_Model::TempWstatus_i,
                                    upperDesiredTempWStatus: Isolette_Data_Model::TempWstatus_i,
                                    internalFailure: Isolette_Data_Model::Failure_Flag_i,
                                    heat_control: Isolette_Data_Model::On_Off
                                  ) -> bool{
    return !(
              lowerDesiredTempWStatus.status == Isolette_Data_Model::ValueStatus::Valid
              && upperDesiredTempWStatus.status == Isolette_Data_Model::ValueStatus::Valid
              && currentTempWStatus.status == Isolette_Data_Model::ValueStatus::Valid
              && regulator_mode == Isolette_Data_Model::Regulator_Mode::Normal_Regulator_Mode
              && currentTempWStatus.degrees < lowerDesiredTempWStatus.degrees
            ) 
            ||
            (
              heat_control == Isolette_Data_Model::On_Off::Onn
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
