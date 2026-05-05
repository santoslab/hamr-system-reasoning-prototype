# Isolette System-level Contract Implemnatation Mockup

TODO
. USER
    . Property in englsih 
    . Property as function
    . Component contracts not enough
    . Express sequence of neccesary component contracts
        . frame conditions
    . Intution of the system assertions
        . some carry post-conditions
        . some do more interesting things
    . Intution of the schema 
. WHAT HAPPENS BEHIND THE SCENES
    . VCs
    . Neccesary changes to the contract
    . Runtime Monitor (Bring it up)
        . State how to run the monitor



## 
















This file provides a mockup of the textual representation of a system-level contract for the Isolette system along with the expected verification conditions and a mockup of a runtime monitor for the system-level specifications. The work presented in this file is based on the [HAMRMicro05](https://github.com/santoslab/hamr-system-reasoning-prototype/tree/main/IsabelleFormalization/HAMRMicro05) formalization of the system-level reasoning framework which is outlined in detail in [System Verification for AADL-based Systems](https://hdl.handle.net/2097/47264).

## Scheduling Contraints

In order to use the system-level reasoning framework it is important to first establish the scheduling contraints for a static cyclic schedule of the system and then translate that into a Workflow net representation of the contraints (A usable and programatic representation of the contraints).

For example we may propose the following scheduling contraints.

### For the System
The components of the System must run in the following order

- The **Operator Interface** must be scheduled before the **Regulator**
- The **Operator Interface** must be scheduled before the **Monitor**
- The **Temp Sensor** must be scheduled before the **Regulator**
- The **Temp Sensor** must be scheduled before the **Monitor**
- The **Regulator** must be scheduled before the **Heat Source**
- The **Monitor** must be scheduled before the **Heat Source**

These contraints can be represented as the following Workflow net

![System Contraints](./Images/SystemContraints.drawio.png)

**<u>NOTE:</u>** The split and join express that all components on one path from the split to the join have no scheduling contraints with respect to any component on any other path. This means that the components on one path can be interleaved with the components on another (e.g., Regualtor and Monitor can be interleaved in the schedule).

This expresses that the possible schedules for the Isolette are 
```
1. OI -> TS -> REG -> MON -> HS
2. OI -> TS -> MON -> REG -> HS
3. TS -> OI -> REG -> MON -> HS
4. TS -> OI -> MON -> REG -> HS
```


### For the Regualtor

The components of the Regulator must run in the following order
1. Detect Regulator Failure (DRF)
2. Manage Regulator Interface (MRI)
3. Manage Regulator Mode (MRM)
4. Manage Heat Source (MHS)

These contraints can be represented as the following Workflow net

![Regulator Contraints](./Images/RegContraints.drawio.png)

This expresses the only schedule for the Regulator is 
```
DRF -> MRI ->  MRM -> MHS
```

### For the Monitor

The components of the Monitor must run in the following order
1. Detect Monitor Failure (DMF)
2. Manage Monitor Interface (MMI)
3. Manage Monitor Mode (MMM)
4. Manage Alarm (MA)

These contraints can be represented as the following Workflow net

![Regulator Contraints](./Images/MonContraints.drawio.png)

This expresses the only schedule for the Monitor is 
```
DMF -> MMI ->  MMM -> MA
```

### Total Workflow Net Representation

Due to several properties, the Workflow nets for the Monitor and Regualtor can be composed with the Workflow net for the System. This new Worflow net represents the scheduling contraints for the system where the Monitor and Regulator are replaced with the components of the subsystems and their respective contraints.

![Composed Contraints](./Images/CompContraints.drawio.png)

This can be also be represented more cleanly as

![Composed Collapsed Contraints](./Images/CompCollapsedContraints.drawio.png)

This expresses that the possible schedules for the Isolette are 
```
1. OI -> TS -> SOME INTERLEAVING OF THE REG AND MON COMPONENTS -> HS
2. TS -> OI -> SOME INTERLEAVING OF THE REG AND MON COMPONENTS -> HS
```

It is important to note that this new representation of the contraints preserves all aforementioned contraints.

## System-level Reasoning

With the addition of a system-level reasoning framework, we want to be able to prove the following system-level properties

* [sysProp_NormalModeHeatOn](https://github.com/santoslab/hamr-system-reasoning-prototype/blob/2d5a999b69915d74aede2239dec4bcf462cada09/IsoletteExample/Aritfacts/TextualContract.txt#L18)
    * Heat Control control laws; NORMAL mode => Heat ON result state
    * After the regualtor finishes execution
* [sysProp_NormalModeAlarmOn](https://github.com/santoslab/hamr-system-reasoning-prototype/blob/2d5a999b69915d74aede2239dec4bcf462cada09/IsoletteExample/Aritfacts/TextualContract.txt#L64)
    * Alarm control laws; NORMAL mode with temp range violation => Alarm ON result state
    * After the monitor finishes execution
* the precondition of all components are satisfied before they execute

### System-level Contracts

The textual system-level contract that express the desired requirement

```
Contract {
	SysAssert {
        Name: START_Assert,
        Assert: True
    },
    SplitJoin {
        Schema { // OI
            SysAssert {
                Name: START_OI_Assert,
                Assert: True
            },
            Component { //assumptions proven
                Name: oi
            },
            SysAssert {
                Name: END_OI_Assert,
                Assert:
                    //derived from component contract
                    sysProp_Allowed_LowerAlarmTempWstatus
                    and sysProp_Allowed_UpperAlarmTempWstatus
                    and sysProp_Allowed_AlarmTempWStatus_Ranges
                    and sysProp_lower_is_not_higher_than_upper
            }
        },
        Schema { // TS
            SysAssert {
                Name: START_TS_Assert,
                Assert: True
            },
            Component { //assumptions proven
                Name: ts
            },
            SysAssert {
                Name: END_TS_Assert,
                Assert: True
            }
        }
    },
    SysAssert {
        Name: Post_TS_OI_Assert,
        Assert:
            //derived from JOIN
            sysProp_Allowed_LowerAlarmTempWstatus
            and sysProp_Allowed_UpperAlarmTempWstatus
            and sysProp_Allowed_AlarmTempWStatus_Ranges
            and sysProp_lower_is_not_higher_than_upper
    },
    SplitJoin {
        Schema { // Regulator
            SysAssert {
                Name: START_Regulator_Assert,
                Assert: 
                    //derived from SPLIT
                    sysProp_lower_is_not_higher_than_upper
            },
            Component { //assumptions proven
                Name: drf
            },
            SysAssert {
                Name: Post_DRF_Assert,
                Assert: 
                    //holds from frame condition
                    sysProp_lower_is_not_higher_than_upper
            },
            Component { //assumptions proven
                Name: mri
            },
            SysAssert {
                Name: Post_MRI_Assert,
                Assert:
                    // derived from component contract
                        sysProp_REQ_MRI_7
                        and sysProp_REQ_MRI_8
                        and sysProp_lower_is_lower_temp
            },
            Component { //assumptions proven
                Name: mrm
            },
            SysAssert {
                Name: Post_MRM_Assert,
                Assert:
                    //holds from frame condition
                    sysProp_REQ_MRI_7
                    and sysProp_REQ_MRI_8
                    and sysProp_lower_is_lower_temp
            },
            Component { //assumptions proven
                Name: mhs
            },
            SysAssert { //look at REQ_MHS_2
                Name: END_Regulator_Assert,
                Assert: 
                    sysProp_NormalModeHeatOnn                
            }
        },
        Schema { //Monitor
            SysAssert {
                Name: START_Monitor_Assert,
                Assert: 
                    //derived from SPLIT
                    sysProp_Allowed_LowerAlarmTempWstatus
                    and sysProp_Allowed_UpperAlarmTempWstatus
                    and sysProp_Allowed_AlarmTempWStatus_Ranges
            },
            Component { //assumptions proven
                Name: dmf
            },
            SysAssert {
                Name: Post_DMF_Assert,
                Assert: 
                    //hold from frame condition
                    sysProp_Allowed_LowerAlarmTempWstatus
                    and sysProp_Allowed_UpperAlarmTempWstatus
                    and sysProp_Allowed_AlarmTempWStatus_Ranges
            },
            Component { //assumptions proven
                Name: mmi
            },
            SysAssert {
                Name: Post_MMI_Assert,
                Assert: 
                    // Dervied from component contract
                        sysProp_REQ_MMI_5
                        and sysProp_REQ_MMI_6
                        and sysProp_Figure_A_7_Weakened
                    // Derived from component contract, write frame, and pre-assertions
                        and sysProp_Table_A_12_LowerAlarmTemp
                        and sysProp_Table_A_12_UpperAlarmTemp
            },
            Component { //assumptions proven
                Name: mmm
            },
            SysAssert { 
                Name: Post_MMM_Assert,
                Assert: 
                    //These are preserved due to frame conditions
                    sysProp_REQ_MMI_5
                    and sysProp_REQ_MMI_6
                    and sysProp_Figure_A_7_Weakened
                    and sysProp_Table_A_12_LowerAlarmTemp
                    and sysProp_Table_A_12_UpperAlarmTemp
            },
            Component { //assumptions proven
                Name: ma
            },
            SysAssert { //look at REQ_MA_2
                Name: END_Monitor_Assert,
                Assert:
                    sysProp_NormalModeAlarmOn
            }
        }
    }
    SysAssert { // HS
        Name: START_HS_Assert,
        Assert: True
    },
    Component { //assumptions proven
        Name: hs
    },
    SysAssert {
        Name: END_Assert,
        Assert: True
    }
}
```

The full contract and all associated functions can be found [here](https://github.com/santoslab/hamr-system-reasoning-prototype/blob/main/IsoletteExample/Aritfacts/TextualContract.txt).

### Verification Conditions

The verification conditions for a system contract are the minimal set of requirements neccesary to verify a system satisfies its contracts. These conditions will be automatically discharged via SMT-based tools in the final system. The formal definition of the verification conditions can be found is the formalization and report found at the top of this file.

This section will provide a high-level explanation of all the VCs along with a full example for each. The full list of VCs can be found [here](https://github.com/santoslab/hamr-system-reasoning-prototype/blob/main/IsoletteExample/Aritfacts/VCs.md).

#### Init-State VC

**<u>Definition:</u>** The initial state of the system satisfies the assertion that can be made at the start of a schedule cycle​.

**<u>Purpose:</u>** This VC verifies that initial state satisfies the requirements of the system before the system begins execution.


**<u>Example:</u>** The Init-State VC for the Isolette system is

```
st satisfies all initialize guarantees
⊢ START_Assert st
```

When expanded this VC becomes

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


#### Pre-Assert VC

**<u>Definition:</u>** Given a pre-state st1 and a post-state st2, where st1 satisfies the pre-assertions of the transition, st2 should satisfy all post-assertions​.

* If the transition is tied to a component, then st1 and st2 need to satisfy the component contract and write frames​

* Else, the transition does not update the state so auxiliary preconditions are not needed (i.e. st1 = st2)​

**<u>Purpose:</u>** This VC is used to verify that executing a transition on a pre-assertion conformant pre-state produces a post-assertion conformant post-state 

**<u>Example:</u>** The Pre-Assert VC for the MHS component is

```
Post_MRM_Assert st
⊢ MHS's Precondition
```

When expanded this VC becomes

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

When expanded this VC becomes

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

#### Post-Pre VC

```
END_Assert
⊢ START_Assert
```

When exapnded the VC becomes

```
True
⊢ True
```

### Necessary Changes to the Component Contract

With the addition of the system contract, it is required that the entire precondition of every component contract is proven to be true so that the component contract can be used on the system-level to describe the behavior of the component. With this change, certain aspects of the components contracts have proven to be either too strong or too weak to enable system-level reasoning. This section will go over the necessary changes.

#### Operator Interface

The issue with the contract for the OI is that it does not specify the relation between the lower_desired_tempWStatus and the upper_desired_tempWStatus. It is neccsary to establish that ```lower_desired_tempWStatus.degrees <= upper_desired_tempWStatus.degrees``` to satisfy the assumption of the MRI. Therefore the follow guarantee is added to the OI compute section of the contract.

```
guarantee Allowed_AlarmTempWStatus_Ranges
    "An integration constraint can only refer to a single port, so need a general requires
    |clause to relate the lower and upper temps":
    GUMBO_Library::GUMBO__Library::Allowed_AlarmTempWStatus_Ranges(lower_alarm_tempWstatus, upper_alarm_tempWstatus);
```

This can be found [here](https://github.com/santoslab/hamr-system-reasoning-prototype/blob/2d5a999b69915d74aede2239dec4bcf462cada09/IsoletteExample/855-s26-isolette-project/isolette/sysml/Operator_Interface.sysml#L134).

#### MRI

The issue with the component contract for the MRI is that the component contract for the MHS requires that ```lower_desired_temp.degrees <= upper_desired_temp.degrees```, but if the MRI fails (interface failure), the desired range in unspecified. To remedy this, a guarantee is added to the MRI component contract in the compute section.

```
guarantee lower_is_lower_temp: lower_desired_temp.degrees <= upper_desired_temp.degrees;
```

This can be found [here](https://github.com/santoslab/hamr-system-reasoning-prototype/blob/2d5a999b69915d74aede2239dec4bcf462cada09/IsoletteExample/855-s26-isolette-project/isolette/sysml/Regulate.sysml#L186).

**<u>NOTE:</u>** This shortcoming can also be remedied by making it so that the MHS is mode aware (i.e., making it so that ```lower_desired_temp.degrees <= upper_desired_temp.degrees``` is only true when the regualotr is in normal mode).

#### MA

The issue with the MA requirement is that the component compute assumption ```Figure_A_7: upper_alarm_temp.degrees - lower_alarm_temp.degrees >= 1``` is too strong for the current requirements of the system. In order to make it so that this assumption can be verified the assumption is weakened to the following requirement.

```
assume Figure_A_7_Weakened: lower_alarm_temp.degrees <= upper_alarm_temp.degrees;
```

This can be found [here](https://github.com/santoslab/hamr-system-reasoning-prototype/blob/2d5a999b69915d74aede2239dec4bcf462cada09/IsoletteExample/855-s26-isolette-project/isolette/sysml/Monitor.sysml#L421-L425).

**<u>NOTE:</u>** This shortcoming can also be remeddied by changing the component contracts of the MMI and OI to ensure that the ```Figure_A_7``` requirement.

#### MMI

The issue with the MMI is similar to the MRI where, Figure_A_7_Weakened needs to be ensured, but when the interface fails, the alarm range in unspecified. To remedy this, the following guarantee is added to the MMI component contract in the compute section.

```
guarantee Figure_A_7_Weakened: lower_alarm_temp.degrees <= upper_alarm_temp.degrees;
```

This can be found [here](https://github.com/santoslab/hamr-system-reasoning-prototype/blob/2d5a999b69915d74aede2239dec4bcf462cada09/IsoletteExample/855-s26-isolette-project/isolette/sysml/Monitor.sysml#L183).

## Runtime Monitor

### How to Run with Docker Container

```
docker run -it --rm -v /PATH/TO/hamr-system-reasoning-prototype/IsoletteExample/855-s26-isolette-project/isolette:/home/microkit/isolette/ 
jasonbelt/microkit_provers bash -ci \
"cd isolette/hamr/microkit && \
MICROKIT_SDK=/home/microkit/provers/microkit-sdk-2.1.0 && \
make clean && \
CONFIG=monitor.mk make qemu"
```