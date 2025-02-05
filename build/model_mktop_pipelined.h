/*
 * Generated by Bluespec Compiler, version 2023.07-33-g1c27a41e (build 1c27a41e)
 * 
 * On Tue May 14 09:28:26 EDT 2024
 * 
 */

/* Generation options: */
#ifndef __model_mktop_pipelined_h__
#define __model_mktop_pipelined_h__

#include "bluesim_types.h"
#include "bs_module.h"
#include "bluesim_primitives.h"
#include "bs_vcd.h"

#include "bs_model.h"
#include "mktop_pipelined.h"

/* Class declaration for a model of mktop_pipelined */
class MODEL_mktop_pipelined : public Model {
 
 /* Top-level module instance */
 private:
  MOD_mktop_pipelined *mktop_pipelined_instance;
 
 /* Handle to the simulation kernel */
 private:
  tSimStateHdl sim_hdl;
 
 /* Constructor */
 public:
  MODEL_mktop_pipelined();
 
 /* Functions required by the kernel */
 public:
  void create_model(tSimStateHdl simHdl, bool master);
  void destroy_model();
  void reset_model(bool asserted);
  void get_version(char const **name, char const **build);
  time_t get_creation_time();
  void * get_instance();
  void dump_state();
  void dump_VCD_defs();
  void dump_VCD(tVCDDumpType dt);
};

/* Function for creating a new model */
extern "C" {
  void * new_MODEL_mktop_pipelined();
}

#endif /* ifndef __model_mktop_pipelined_h__ */
