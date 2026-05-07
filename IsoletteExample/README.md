# Isolette Example

## Artifact Links

**Shortcuts to Artifacts**

|                                   | Location |
|-----------------------------------|----------|
| Isolette SysML Model              |   [SysML Model](https://github.com/santoslab/hamr-system-reasoning-prototype/tree/main/IsoletteExample/855-s26-isolette-project/isolette/sysml)   |
| Isolette Microkit Implementation  |   [Microkit Implementation](https://github.com/santoslab/hamr-system-reasoning-prototype/tree/main/IsoletteExample/855-s26-isolette-project/isolette/hamr/microkit)   |
| System Contract / Schedule Schema |   [TextualContract.txt](https://github.com/santoslab/hamr-system-reasoning-prototype/blob/main/IsoletteExample/Aritfacts/TextualContract.txt)   |
| Verification Conditions           |   [VCs.md](https://github.com/santoslab/hamr-system-reasoning-prototype/blob/main/IsoletteExample/Aritfacts/VCs.md)   |
| Runtime Monitor                   |   [monitor_process_monitor_thread_app.rs](https://github.com/santoslab/hamr-system-reasoning-prototype/blob/main/IsoletteExample/855-s26-isolette-project/isolette/hamr/microkit/crates/monitor_process_monitor_thread/src/component/monitor_process_monitor_thread_app.rs)   |
| Example Walkthrough               |   [ExampleWalkthrough.md](https://github.com/santoslab/hamr-system-reasoning-prototype/blob/main/IsoletteExample/Aritfacts/ExampleWalkthrough.md)   |

**NOTE:** The runtime monitor assumes the following static cyclic schedule:

```
TS -> OI -> DMF -> MMI -> MMM -> MA -> DRF -> MRI -> MRM -> MHS -> HS
```
---

## Scheduling Constraints

All properties use the following scheduling contraints for a static cyclic schedule provided by [TextualContract.txt](./Aritfacts/TextualContract.txt).

### Global Ordering Constraints

- Operator Interface executes before Regulator
- Operator Interface executes before Monitor
- Temperature Sensor executes before Regulator
- Temperature Sensor executes before Monitor
- Regulator executes before Heat Source
- Monitor executes before Heat Source

### Regulator Subsystem Ordering

The following components must execute in order:

1. DRF
2. MRI
3. MRM
4. MHS

### Monitor Subsystem Ordering

The following components must execute in order:

1. DMF
2. MMI
3. MMM
4. MA

---

## System Properties

### `sysProp_NormalModeHeatOnn`

|                           |   |
|---------------------------|---|
| Description               | Heat Control control laws; NORMAL mode => Heat ON result state  |
| Property Type | End-to-End property for the Regulator subsystem |
| System Testing Equivalent | [HC__Normal_____Heat_On](https://github.com/santoslab/hamr-system-testing-case-studies/blob/main/isolette/hamr/slang/src/test/system/isolette/system_tests/rst/Regulate_Subsystem_Test_wSlangCheck.scala#L92)  |
| Evaluation Point | After the Regulator has finished exeuction (After `MHS`)|
| Contract Property         | [sysProp_NormalModeHeatOnn](https://github.com/santoslab/hamr-system-reasoning-prototype/blob/0b9b41c6eb179b7ce90adef89eb5b2bf1feaa27f/IsoletteExample/Aritfacts/TextualContract.txt#L29) |
| Contract Assertion Location         |  [END_Regulator_Assert](https://github.com/santoslab/hamr-system-reasoning-prototype/blob/0b9b41c6eb179b7ce90adef89eb5b2bf1feaa27f/IsoletteExample/Aritfacts/TextualContract.txt#L339) |
| Executable Property     |  [sysProp_NormalModeHeatOnn](https://github.com/santoslab/hamr-system-reasoning-prototype/blob/0b9b41c6eb179b7ce90adef89eb5b2bf1feaa27f/IsoletteExample/855-s26-isolette-project/isolette/hamr/microkit/crates/monitor_process_monitor_thread/src/component/monitor_process_monitor_thread_app.rs#L794) |
| Runtime Monitor Location  |  [END_Regulator_Assert](https://github.com/santoslab/hamr-system-reasoning-prototype/blob/0b9b41c6eb179b7ce90adef89eb5b2bf1feaa27f/IsoletteExample/855-s26-isolette-project/isolette/hamr/microkit/crates/monitor_process_monitor_thread/src/component/monitor_process_monitor_thread_app.rs#L521) |

### `sysProp_NormalModeAlarmOn`

|                           |   |
|---------------------------|---|
| Description               | Alarm control laws; NORMAL mode with temp range violation => Alarm ON result state  |
| Property Type | End-to-End property for the Monitor subsystem  |
| System Testing Equivalent | [MA__Normal_____Alarm_On](https://github.com/santoslab/hamr-system-testing-case-studies/blob/main/isolette/hamr/slang/src/test/system/isolette/system_tests/monitor1/Monitor_Subsystem_Test_wSlangCheck.scala#L85)  |
| Evaluation Point | After the Monitor has finished exeuction (After `MA`)|
| Contract Property         | [sysProp_NormalModeAlarmOn](https://github.com/santoslab/hamr-system-reasoning-prototype/blob/0b9b41c6eb179b7ce90adef89eb5b2bf1feaa27f/IsoletteExample/Aritfacts/TextualContract.txt#L104) |
| Contract Assertion Location         | [END_Monitor_Assert](https://github.com/santoslab/hamr-system-reasoning-prototype/blob/0b9b41c6eb179b7ce90adef89eb5b2bf1feaa27f/IsoletteExample/Aritfacts/TextualContract.txt#L395) |
| Executable Property      | [sysProp_NormalModeAlarmOn](https://github.com/santoslab/hamr-system-reasoning-prototype/blob/0b9b41c6eb179b7ce90adef89eb5b2bf1feaa27f/IsoletteExample/855-s26-isolette-project/isolette/hamr/microkit/crates/monitor_process_monitor_thread/src/component/monitor_process_monitor_thread_app.rs#L694) |
| Runtime Monitor Location  | [END_Monitor_Assert](https://github.com/santoslab/hamr-system-reasoning-prototype/blob/0b9b41c6eb179b7ce90adef89eb5b2bf1feaa27f/IsoletteExample/855-s26-isolette-project/isolette/hamr/microkit/crates/monitor_process_monitor_thread/src/component/monitor_process_monitor_thread_app.rs#L573) |



