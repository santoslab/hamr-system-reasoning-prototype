## HAMR Micro 04 Description

### Purpose

The purpose of this "model sketch" of HAMR semantics is to explore the
design of system property specification and verification framework for
HAMR.

The key technical features of this limited semantics model including a
modeling language and execution framework with 
- a collection of atomic tasks (similar to previous HAMR Micro models) but
  extended to include input/output ports and true task-local state
  (instead of just having the tasks write to a global store).
- ports and the inter-task communication infrastructure is simplified
  by have inter-task channels modeled as variable holding single data
  values that can be read or written by tasks.  Each task explicitly 
  declares the channels that they will read or write.
- in previous models, the global store was model as a record, which
  made specification of task behaviors and the semantics simple, but
  it did not easily allow statement of frame conditions or properties
  that relied on quantification across ports and variables.  Moreover,
  in this model, we want to prototype the general notion of
  "observation" which is a snapshot of a subset of a system state.
  That concept (essentially subseting of system-wide set of variables)
  cannot easily be modeled using a single record type.  Finally, by
  introducing variable ids and channel ids with seperate state
  storage, we move closer to the structure of the full HAMR model.
- there is no explicit communication propagation step as in HAMR.
  Instead, the action of a task just updates channels which can
  subsequently be read by other tasks.
- tasks are scheduled with a static schedule (as in previous HAMR
  micro models). There is no initialization phase.  Instead, the
  system is "started" with an initial state for each component and for
  the global communication substrate.

This model enables explorations of the following new concepts:
- **More realistic contracts**: Previous HAMR micro models introduced a basic notion of contract
  with pre/post-conditions.  However, those only applied to a global
  store.  This model moves closer to full HAMR by enabling contracts
  that apply to input/output ports and local variables.
- **State observations**: We will prototype a notion of state observation
  (snapshots of subsets of the system state) and phrase system
  properties in terms of these.

After this model is completed, there are two significant additional
features that will need to be added (e.g., HAMR micro 5,6?).  These
are required for us to fully prototype the HAMR system verification framework.
- component hierarchy (nesting of components to model AADL subsystems,
  etc.)
- explicit scheduling of communication steps

### Next Steps

#### Example Models

- (Jacob) Develop example models.  Try modeling pieces of the
  Isolette (though if this feels too complex for a first go,
  make something simpler first). For example, try modeling simplified versions of the three
  components of the Regulate subsystem (manage regulate mode, manage
  regulate interface, manage heat source).  Simplify by
   - omitting notions of internal error
   - all temperature values are integers (initially, ignore the
     concept of value status; later a "failed" status can be modeled
     as a negative integer)
   - omit the notion of mode first, and just focus on upper desired
     temp, lower desired temp, current temp, heat control (mode,
     represented as an integer can be added later)
   - make a simple static schedule following the same order as in the
     real Isolette (manage interface, manage mode, manage heat source)  

#### Well-formedness Conditions
- (Jacob) complete the well-formedness conditions on models.  Develop
  proofs that your example models are well-formed

#### Task Actions and Initial State
- (Jacob) develop task actions for the example system (especially the
  Isolette) that correspond to simplified versions of the real
  Isolette.
- (Jacob) develop versions of the initial system state

#### Execution Semantics
- (Jacob) adapt the execution semantics of previous HAMR micro models
  to the new structures
- (Jacob) prove that state well-formedness properties are preserved by
  the execution semantics

#### Observation Framework
- (John/Stefan) design observation framework.  The framework should
   support a semantics for both static verification and run-time
   monitoring.  Figure out how observations get represented along with
   "regular" system states in the semantics.  Note that we may way to
   tie the notion of observations to a logging framework in the full
   HAMR implementation.
- (John) mock up example observation and property declarations for the
  full Isolette AADL model -- illustrating possible "system property" extensions to the
  GUMBO language.

#### Property Specification Framework
- (John/Stefan/Jacob) - driven by examples from the Isolette and
  Firewall systems, design specification framework for properties that
  span multiple components.  We need to be able to verify and perform 
  run-time monitoring on system properties for the above systems.

  