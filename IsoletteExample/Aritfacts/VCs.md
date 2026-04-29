# Verification Conditions

## After Initialization

### Initial State VC

```
st satisfies all initialize guarantees
⊢ START_Assert st
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
⊢ All assumes of OI hold for st
```

### Next-Assert VC

```
START_OI_Assert st1
^ OI_LocalWriteFrame st1 st2
^ OI_GlobalWriteFrame st1 st2
^ All non-initialize guarantees, compute cases, and invariants for OI hold for st1 and st2
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
⊢ All assumes of MRI hold for st
```

#### Next-Assert VC

```
Post_DRF_Assert st1
^ MRI_LocalWriteFrame st1 st2
^ MRI_GlobalWriteFrame st1 st2
^ All non-initialize guarantees, compute cases, and invariants for MRI hold for st1 and st2
⊢ Post_MRI_Assert st2
```

### Manage Regulator Mode

#### Pre-Assert VC

```
Post_MRI_Assert st
⊢ All assumes of MRM hold for st
```

#### Next-Assert VC

```
Post_MRI_Assert st1
^ MRM_LocalWriteFrame st1 st2
^ MRM_GlobalWriteFrame st1 st2
^ All non-initialize guarantees, compute cases, and invariants for MRM hold for st1 and st2
⊢ Post_MRM_Assert st2
```

### Manage Heat Source

#### Pre-Assert VC

```
Post_MRM_Assert st
⊢ All assumes of MRM hold for st
```


#### Next-Assert VC

```
Post_MRM_Assert st1
^ MHS_LocalWriteFrame st1 st2
^ MHS_GlobalWriteFrame st1 st2
^ All non-initialize guarantees, compute cases, and invariants for MHS hold for st1 and st2
⊢ END_Regulator_Assert st2
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
⊢ All assumes of MMI hold for st
```

#### Next-Assert VC

```
Post_DMF_Assert st1
^ MMI_LocalWriteFrame st1 st2
^ MMI_GlobalWriteFrame st1 st2
^ All non-initialize guarantees, compute cases, and invariants for MMI hold for st1 and st2
⊢ Post_MMI_Assert st2
```

### Manage Monitor Mode

#### Pre-Assert VC

```
Post_MMI_Assert st
⊢ All assumes of MMM hold for st
```

#### Next-Assert VC

```
Post_MMI_Assert st1
^ MMM_LocalWriteFrame st1 st2
^ MMM_GlobalWriteFrame st1 st2
^ All non-initialize guarantees, compute cases, and invariants for MMM hold for st1 and st2
⊢ Post_MMM_Assert st2
```

### Manage Alarm

#### Pre-Assert VC

```
Post_MMM_Assert st
⊢ All assumes of MA hold for st
```

#### Next-Assert VC

```
Post_MMM_Assert st1
^ MA_LocalWriteFrame st1 st2
^ MA_GlobalWriteFrame st1 st2
^ All non-initialize guarantees, compute cases, and invariants for MA hold for st1 and st2
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
END_Assert
⊢ START_Assert
```


