# Research Plan for 855 Spring 2026 Isolette Project

## Getting Familiar With The Files

- Open `isolette/sysml` in CodeIVE and make sure that you can browse the models appropriately.  The top-level model for the system is in `Isolette.sysml`

- In `hamr/microkit`, find the crate for the Manage Heat Source component `isolette/hamr/microkit/crates/thermostat_rt_mhs_mhs`.  Make sure that you can run versus on the Rust code via `make verus` and that you can run the tests from both `make test` and from within the IVE.

## Read Appendix A of the FAA REMH

- Read appendix A of the [FAA REMH](https://www.faa.gov/sites/faa.gov/files/aircraft/air_cert/design_approvals/air_software/AR-08-32.pdf).  This is the information from which the Isolette implementation was derived.

- Work through every component in the Monitor and Regulate subsystems.  For each component, compare the documented requirements to the GUMBO contracts in the SysMLv2 model.  The look at the crate code for the component, and study..
  - component application code
  - component verus contracts
  - component tests

Make notes about each component, especially noting if there are tests that need to be added.

## Preliminary Designs and Requirements

Make preliminary architecture designs for how you would change the model files for each of the planned extensions
  - redundant sensors
  - infant temperature sensor
  - cooling unit

## Redundant Sensors Requirements

Following the same style as requirements for each component in the REMH, write natural language requirements for the redundant sensors component.
Place these in the file `isolette/requirements/redundant_temp_sensors.md`



