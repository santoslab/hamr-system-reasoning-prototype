# Verification Conditions

For the pruposes of the document st1 and st2 are arbitrary states where st1 is the pre-state of a component transition and st2 is the post-state of a component transition. Values from st1 will be deliniated as old(variable/channel name) and all values from st2 will just be variable/channel name.

## After Initialization

### Initial State VC

```
st satisfies all initialize guarantees
⊢ START_Assert st
```

When exanded the result is

```
// OI
I_Guar_lower_alarm_tempWstatus(lower_alarm_tempWstatus)
^ I_Guar_upper_alarm_tempWstatus(upper_alarm_tempWstatus)

// MRI
^ initialize_RegulatorStatusIsInitiallyInit(regulator_status)

// MRM
^ initialize_REQ_MRM_1(api_regulator_mode)

// MHS
^ initialize_initlastCmd(lastCmd) &&
^ initialize_REQ_MHS_1(heat_control)

// MMI
^ initialize_monitorStatusInitiallyInit(monitor_status)

// MMM
^ initialize_REQ_MMM_1(monitor_mode)

// MA
^ initialize_REQ_MA_1(lastCmd, alarm_control)

⊢ True
```

## Before OI and TS

### Next-Assert VC

```
START_Assert st ⊢ START_OI_Assert st
```

```
START_Assert st ⊢ START_TS_Assert st
```

## Operatore Interface

### Pre-Assert VC

```
START_OI_Assert st
⊢ OI's Precondition
```

### Next-Assert VC

```
START_OI_Assert st1
^ OI_LocalWriteFrame st1 st2
^ OI_GlobalWriteFrame st1 st2
^ OI's Postcondition
⊢ END_OI_Assert st2
```

## Temp Sensor

### Pre-Assert VC

```
START_TS_Assert st
⊢ True (* Temp Sensor has no contract *)
```

### Next-Assert VC

```
START_TS_Assert st1
^ TS_LocalWriteFrame st1 st2
^ TS_GlobalWriteFrame st1 st2
^ True (* Temp Sesnor has no contract *)
⊢ END_TS_Assert st2
```

## After Temp Sensor and Operator Interface

### Next-Assert VC

```
END_TS_Assert st
^ END_OI_Assert st
⊢ Post_TS_OI_Assert st
```

## Before Regualtor and Monitor

### Next-Assert VC

```
Post_TS_OI_Assert st ⊢ START_Regulator_Assert st
```

```
Post_TS_OI_Assert st ⊢ START_Monitor_Assert st
```

## Regulator

### Detect Regulator Failure

#### Pre-Assert VC

```
START_Regulator_Assert st
⊢ True (* DRF has no contract *)
```

#### Next-Assert VC

```
START_Regulator_Assert st1
^ DRF_LocalWriteFrame st1 st2
^ DRF_GlobalWriteFrame st1 st2
^ True (* DRF has no contract *)
⊢ Post_DRF_Assert st2
```

### Manage Regulator Interface

#### Pre-Assert VC

```
Post_DRF_Assert st
⊢ MRI's Precondition
```

#### Next-Assert VC

```
Post_DRF_Assert st1
^ MRI_LocalWriteFrame st1 st2
^ MRI_GlobalWriteFrame st1 st2
^ MRI's Postcondition
⊢ Post_MRI_Assert st2
```

### Manage Regulator Mode

#### Pre-Assert VC

```
Post_MRI_Assert st
⊢ MRM's Precondition
```

#### Next-Assert VC

```
Post_MRI_Assert st1
^ MRM_LocalWriteFrame st1 st2
^ MRM_GlobalWriteFrame st1 st2
^ MRM's Postcondition
⊢ Post_MRM_Assert st2
```

### Manage Heat Source

#### Pre-Assert VC

```
Post_MRM_Assert st
⊢ MHS's Precondition
```

When fully expanded this becomes

```
// Pre-assertions of MHS
sysProp_REQ_MRI_7(lower_desired_tempWstatus,  upper_desired_tempWstatus, interface_failure)
^ sysProp_REQ_MRI_8(lower_desired_tempWstatus, upper_desired_tempWstatus, lower_desired_temp, upper_desired_temp, interface_failure)
^ sysProp_lower_is_lower_temp(lower_desired_temp, upper_desired_temp)
⊢ compute_spec_lower_is_lower_temp_assume(lower_desired_temp, upper_desired_temp)
```


#### Next-Assert VC

```
Post_MRM_Assert st1
^ MHS_LocalWriteFrame st1 st2
^ MHS_GlobalWriteFrame st1 st2
^ MHS's Postcondition
⊢ END_Regulator_Assert st2
```

When fully exapnded this becomes

```
// Pre-assertions of MHS (Post_MRM_Assert)
sysProp_REQ_MRI_7(old(lower_desired_tempWstatus), old(upper_desired_tempWstatus), old(interface_failure))
^ sysProp_REQ_MRI_8(old(lower_desired_tempWstatus), old(upper_desired_tempWstatus), old(lower_desired_temp), old(upper_desired_temp), old(interface_failure))
^ sysProp_lower_is_lower_temp(old(lower_desired_temp), old(upper_desired_temp))

// Local Write Frame
^ MHS_LocalWriteFrame st1 st2 (* Not ceccesary to expand *)

// Global Write Frame
^ old(lower_desired_tempWstatus) == lower_desired_tempWstatus
^ old(upper_desired_tempWstatus) == upper_desired_tempWstatus
^ old(lower_desired_temp) == lower_desired_temp
^ old(upper_desired_temp) == upper_desired_temp
^ old(interface_failure) == interface_failure
^ old(regulator_mode) == regulator_mode
^ ... (* Truncated global write frame for brevity *)

// Component Post-coniditon (Compute Guarantee)
^ compute_spec_lastCmd_guarantee(lastCmd, heat_control)

// Component Post-condition (Compute Cases)
^ compute_case_REQ_MHS_1(old(regulator_mode), heat_control);
^ compute_case_REQ_MHS_2(old(current_tempWstatus), old(lower_desired_temp), old(regulator_mode), heat_control);
^ compute_case_REQ_MHS_3(old(current_tempWstatus), old(regulator_mode), old(upper_desired_temp), heat_control);
^ compute_case_REQ_MHS_4(old(lastCmd), old(current_tempWstatus), old(lower_desired_temp), old(regulator_mode), old(upper_desired_temp), heat_control);
^ compute_case_REQ_MHS_5(old(regulator_mode), heat_control);
⊢ sysProp_NormalModeHeatOnn(regulator_mode, currentTempWStatus, lowerDesiredTempWStatus, upperDesiredTempWStatus, internalFailure, heat_control)  
```

## Monitor

### Detect Monitor Failure

#### Pre-Assert VC

```
START_Monitor_Assert st
⊢ True (* DMF has no contract *)
```

#### Next-Assert VC

```
START_Monitor_Assert st1
^ DMF_LocalWriteFrame st1 st2
^ DMF_GlobalWriteFrame st1 st2
^ True (* DMF has no contract *)
⊢ Post_DMF_Assert st2
```

### Manage Monitor Interface

#### Pre-Assert VC

```
Post_DMF_Assert st
⊢ MMI's Precondition
```

#### Next-Assert VC

```
Post_DMF_Assert st1
^ MMI_LocalWriteFrame st1 st2
^ MMI_GlobalWriteFrame st1 st2
^ MMI's Postcondition
⊢ Post_MMI_Assert st2
```

### Manage Monitor Mode

#### Pre-Assert VC

```
Post_MMI_Assert st
⊢ MMM's Precondition
```

#### Next-Assert VC

```
Post_MMI_Assert st1
^ MMM_LocalWriteFrame st1 st2
^ MMM_GlobalWriteFrame st1 st2
^ MMM's Postcondition
⊢ Post_MMM_Assert st2
```

### Manage Alarm

#### Pre-Assert VC

```
Post_MMM_Assert st
⊢ MA's Precondition
```

#### Next-Assert VC

```
Post_MMM_Assert st1
^ MA_LocalWriteFrame st1 st2
^ MA_GlobalWriteFrame st1 st2
^ MA's Postcondition
⊢ END_Monitor_Assert st2
```

## After Monitor and Regulator

### Next-Assert VC

```
END_Monitor_Assert st
^ END_Regulator_Assert st
⊢ 
START_HS_Assert st
```

## Heat Source

### Pre-Assert VC

```
START_HS_Assert st
⊢ True (* HS has no contract *)
```

### Next-Assert VC

```
START_HS_Assert st1
^ HS_LocalWriteFrame st1 st2
^ HS_GlobalWriteFrame st1 st2
^ True (* Heat Source has no contract *)
⊢ END_Assert st2
```

## End of Cycle

### Post-Pre VC

```
END_Assert st
⊢ START_Assert st
```

When expanded the result is

```
True
⊢ True
```



