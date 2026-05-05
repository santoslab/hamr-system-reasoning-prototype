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


# System Property Walkthrough

This document walks through how a non-trivial system-level property for the Isolette is specified, what conditions are required to verify it, and how it can be checked at runtime.

The work presented here is based on the [HAMRMicro05](https://github.com/santoslab/hamr-system-reasoning-prototype/tree/main/IsabelleFormalization/HAMRMicro05) formalization of the system-level reasoning framework which is outlined in detail in [System Verification for AADL-based Systems](https://hdl.handle.net/2097/47264).


## Problem Overview
### Property (Plain English)
### Why This Is Non-Trivial

## Formal Specification
### Property as a Function
### Limits of Component Contracts

## System-Level Reasoning
### Sequencing Component Contracts

* Important to note that the components may not happens in back to back in the schedule but the ordering still matters (This can be used to express the need for frame conditions as they are neccesary to prove the preservation of facts)

### Frame Conditions

## Understanding the Assertions
### Types of Assertions
### What Each Assertion Enforces

## Schedule Schemas and System Contracts
* Express we have some set of constraints
    * Our neccesary sequence of components is a sequence of constraints
* Present the schema and contract
    * Explain what things do like split join
    * Explain how this seperates our reasoning of subsystems such that we don't care about interleaving (explain the syntatic constraint of independence)
    * Explain how this seperates our need to reason about a subsystem away from the system as a whole
* Trace our needed assertions over the contract until the property is achieved

## Behind the Scenes
### Verification Conditions (VCs)
### Required Contract Changes
## Runtime Monitoring
### What the Monitor Checks
### How to Run the Monitor
### Expected Behavior / Output