/*
 * Generated by Bluespec Compiler, version 2023.07-33-g1c27a41e (build 1c27a41e)
 * 
 * On Tue May 14 09:28:26 EDT 2024
 * 
 */

/* Generation options: */
#ifndef __mkCache32_ins_h__
#define __mkCache32_ins_h__

#include "bluesim_types.h"
#include "bs_module.h"
#include "bluesim_primitives.h"
#include "bs_vcd.h"


/* Class declaration for the mkCache32_ins module */
class MOD_mkCache32_ins : public Module {
 
 /* Clock handles */
 private:
  tClock __clk_handle_0;
 
 /* Clock gate handles */
 public:
  tUInt8 *clk_gate[0];
 
 /* Instantiation parameters */
 public:
 
 /* Module state */
 public:
  MOD_BRAM<tUInt8,tUWide,tUInt64> INST_bdata_memory;
  MOD_Reg<tUInt8> INST_bdata_serverAdapter_cnt;
  MOD_Wire<tUInt8> INST_bdata_serverAdapter_cnt_1;
  MOD_Wire<tUInt8> INST_bdata_serverAdapter_cnt_2;
  MOD_Wire<tUInt8> INST_bdata_serverAdapter_cnt_3;
  MOD_Reg<tUInt8> INST_bdata_serverAdapter_outData_beforeDeq;
  MOD_Reg<tUInt8> INST_bdata_serverAdapter_outData_beforeEnq;
  MOD_Wire<tUInt8> INST_bdata_serverAdapter_outData_dequeueing;
  MOD_Wire<tUWide> INST_bdata_serverAdapter_outData_enqw;
  MOD_Fifo<tUWide> INST_bdata_serverAdapter_outData_ff;
  MOD_Reg<tUInt8> INST_bdata_serverAdapter_s1;
  MOD_Wire<tUInt8> INST_bdata_serverAdapter_s1_1;
  MOD_Wire<tUInt8> INST_bdata_serverAdapter_writeWithResp;
  MOD_BRAM<tUInt8,tUInt8,tUInt8> INST_bstate_memory;
  MOD_Reg<tUInt8> INST_bstate_serverAdapter_cnt;
  MOD_Wire<tUInt8> INST_bstate_serverAdapter_cnt_1;
  MOD_Wire<tUInt8> INST_bstate_serverAdapter_cnt_2;
  MOD_Wire<tUInt8> INST_bstate_serverAdapter_cnt_3;
  MOD_Reg<tUInt8> INST_bstate_serverAdapter_outData_beforeDeq;
  MOD_Reg<tUInt8> INST_bstate_serverAdapter_outData_beforeEnq;
  MOD_Wire<tUInt8> INST_bstate_serverAdapter_outData_dequeueing;
  MOD_Wire<tUInt8> INST_bstate_serverAdapter_outData_enqw;
  MOD_Fifo<tUInt8> INST_bstate_serverAdapter_outData_ff;
  MOD_Reg<tUInt8> INST_bstate_serverAdapter_s1;
  MOD_Wire<tUInt8> INST_bstate_serverAdapter_s1_1;
  MOD_Wire<tUInt8> INST_bstate_serverAdapter_writeWithResp;
  MOD_BRAM<tUInt8,tUInt32,tUInt8> INST_btag_memory;
  MOD_Reg<tUInt8> INST_btag_serverAdapter_cnt;
  MOD_Wire<tUInt8> INST_btag_serverAdapter_cnt_1;
  MOD_Wire<tUInt8> INST_btag_serverAdapter_cnt_2;
  MOD_Wire<tUInt8> INST_btag_serverAdapter_cnt_3;
  MOD_Reg<tUInt8> INST_btag_serverAdapter_outData_beforeDeq;
  MOD_Reg<tUInt8> INST_btag_serverAdapter_outData_beforeEnq;
  MOD_Wire<tUInt8> INST_btag_serverAdapter_outData_dequeueing;
  MOD_Wire<tUInt32> INST_btag_serverAdapter_outData_enqw;
  MOD_Fifo<tUInt32> INST_btag_serverAdapter_outData_ff;
  MOD_Reg<tUInt8> INST_btag_serverAdapter_s1;
  MOD_Wire<tUInt8> INST_btag_serverAdapter_s1_1;
  MOD_Wire<tUInt8> INST_btag_serverAdapter_writeWithResp;
  MOD_Fifo<tUWide> INST_curReq;
  MOD_Fifo<tUWide> INST_hitq;
  MOD_Fifo<tUWide> INST_memReq;
  MOD_Fifo<tUWide> INST_memResp;
  MOD_Reg<tUInt8> INST_state;
 
 /* Constructor */
 public:
  MOD_mkCache32_ins(tSimStateHdl simHdl, char const *name, Module *parent);
 
 /* Symbol init methods */
 private:
  void init_symbols_0();
 
 /* Reset signal definitions */
 private:
  tUInt8 PORT_RST_N;
 
 /* Port definitions */
 public:
  tUWide PORT_putFromProc_e;
  tUWide PORT_putFromMem_e;
  tUWide PORT_getToProc;
  tUWide PORT_getToMem;
 
 /* Publicly accessible definitions */
 public:
  tUInt8 DEF_IF_bstate_serverAdapter_outData_ff_i_notEmpty__ETC___d155;
  tUInt8 DEF_btag_serverAdapter_s1___d83;
  tUInt8 DEF_bstate_serverAdapter_s1___d34;
  tUInt8 DEF_bstate_serverAdapter_outData_enqw_wget____d7;
  tUInt8 DEF_bdata_serverAdapter_outData_ff_i_notEmpty____d102;
  tUInt8 DEF_btag_serverAdapter_cnt_3_whas____d62;
  tUInt8 DEF_btag_serverAdapter_cnt_2_whas____d60;
  tUInt8 DEF_btag_serverAdapter_cnt_1_whas____d59;
  tUInt8 DEF_btag_serverAdapter_outData_ff_i_notEmpty____d53;
  tUInt8 DEF_bstate_serverAdapter_cnt_3_whas____d12;
  tUInt8 DEF_bstate_serverAdapter_cnt_2_whas____d10;
  tUInt8 DEF_bstate_serverAdapter_cnt_1_whas____d9;
  tUInt8 DEF_bstate_serverAdapter_outData_ff_i_notEmpty____d4;
  tUInt8 DEF_btag_serverAdapter_s1_3_BIT_0___d84;
  tUInt8 DEF_bstate_serverAdapter_s1_4_BIT_0___d35;
  tUInt8 DEF_IF_bstate_serverAdapter_outData_ff_i_notEmpty__ETC___d176;
  tUInt8 DEF_curReq_first__58_BITS_63_TO_45_59_EQ_IF_btag_s_ETC___d162;
  tUInt8 DEF_x__h11047;
  tUInt8 DEF_IF_bstate_serverAdapter_outData_ff_i_notEmpty__ETC___d154;
  tUInt8 DEF_NOT_curReq_first__58_BITS_67_TO_64_64_EQ_0_65___d170;
  tUInt8 DEF_NOT_IF_bstate_serverAdapter_outData_ff_i_notEm_ETC___d163;
  tUWide DEF_curReq_first____d158;
  tUInt32 DEF_x_wget__h2238;
  tUInt32 DEF_x_first__h2123;
  tUInt8 DEF_b__h7921;
  tUInt8 DEF_b__h2731;
  tUInt8 DEF_b__h1263;
  tUInt8 DEF_bdata_serverAdapter_s1___d131;
  tUInt8 DEF_state__h10578;
  tUInt8 DEF_bdata_serverAdapter_cnt_3_whas____d110;
  tUInt8 DEF_bdata_serverAdapter_cnt_2_whas____d108;
  tUInt8 DEF_bdata_serverAdapter_cnt_1_whas____d107;
  tUInt32 DEF_x3__h17639;
  tUInt8 DEF_bdata_serverAdapter_s1_31_BIT_0___d132;
  tUInt8 DEF_curReq_first__58_BITS_67_TO_64_64_EQ_0___d165;
  tUInt32 DEF_v__h10698;
  tUInt32 DEF_x__h2336;
  tUInt8 DEF_btag_serverAdapter_cnt_5_SLT_3___d330;
  tUInt8 DEF_bdata_serverAdapter_cnt_13_SLT_3___d167;
  tUInt8 DEF_bstate_serverAdapter_cnt_5_SLT_3___d166;
 
 /* Local definitions */
 private:
  tUInt8 DEF__0_CONCAT_DONTCARE___d25;
  tUInt8 DEF_x__h20566;
  tUInt8 DEF_x__h11218;
  tUWide DEF_bdata_serverAdapter_outData_enqw_wget____d105;
  tUWide DEF_bdata_serverAdapter_outData_ff_first____d246;
  tUWide DEF_bdata_memory_read____d138;
  tUWide DEF_memResp_first____d340;
  tUWide DEF_hitq_first____d415;
  tUInt8 DEF_x2__h11103;
  tUWide DEF_IF_IF_bstate_serverAdapter_outData_ff_i_notEmp_ETC___d323;
  tUWide DEF_IF_btag_serverAdapter_outData_ff_i_notEmpty__3_ETC___d320;
  tUWide DEF_curReq_first__58_BITS_63_TO_0_21_CONCAT_DONTCARE___d322;
  tUWide DEF_IF_curReq_first__58_BITS_67_TO_64_64_EQ_0_65_T_ETC___d406;
  tUWide DEF_IF_curReq_first__58_BITS_37_TO_34_98_EQ_15_01__ETC___d405;
  tUWide DEF_toMemData__h11009;
  tUWide DEF_IF_bdata_serverAdapter_outData_enqw_whas__9_TH_ETC___d318;
  tUInt8 DEF_curReq_first__58_BITS_37_TO_34_98_EQ_0___d239;
  tUInt8 DEF_curReq_first__58_BITS_37_TO_34_98_EQ_1___d237;
  tUInt8 DEF_curReq_first__58_BITS_37_TO_34_98_EQ_2___d234;
  tUInt8 DEF_curReq_first__58_BITS_37_TO_34_98_EQ_3___d232;
  tUInt8 DEF_curReq_first__58_BITS_37_TO_34_98_EQ_4___d229;
  tUInt8 DEF_curReq_first__58_BITS_37_TO_34_98_EQ_5___d227;
  tUInt8 DEF_curReq_first__58_BITS_37_TO_34_98_EQ_6___d224;
  tUInt8 DEF_curReq_first__58_BITS_37_TO_34_98_EQ_7___d222;
  tUInt8 DEF_curReq_first__58_BITS_37_TO_34_98_EQ_8___d219;
  tUInt8 DEF_curReq_first__58_BITS_37_TO_34_98_EQ_9___d217;
  tUInt8 DEF_curReq_first__58_BITS_37_TO_34_98_EQ_10___d214;
  tUInt8 DEF_curReq_first__58_BITS_37_TO_34_98_EQ_11___d212;
  tUInt8 DEF_curReq_first__58_BITS_37_TO_34_98_EQ_12___d209;
  tUInt8 DEF_curReq_first__58_BITS_37_TO_34_98_EQ_13___d207;
  tUInt8 DEF_curReq_first__58_BITS_37_TO_34_98_EQ_15___d201;
  tUInt8 DEF_curReq_first__58_BITS_37_TO_34_98_EQ_14___d204;
  tUInt8 DEF_NOT_curReq_first__58_BITS_37_TO_34_98_EQ_15_01___d313;
  tUWide DEF__0_CONCAT_curReq_first__58_BITS_63_TO_0_21_CONC_ETC___d328;
  tUWide DEF_IF_bstate_serverAdapter_outData_ff_i_notEmpty__ETC___d324;
  tUWide DEF_IF_curReq_first__58_BITS_37_TO_34_98_EQ_15_01__ETC___d402;
  tUWide DEF_IF_curReq_first__58_BITS_37_TO_34_98_EQ_15_01__ETC___d241;
  tUWide DEF_IF_curReq_first__58_BITS_37_TO_34_98_EQ_15_01__ETC___d236;
  tUWide DEF_IF_curReq_first__58_BITS_37_TO_34_98_EQ_15_01__ETC___d399;
  tUWide DEF_IF_curReq_first__58_BITS_37_TO_34_98_EQ_15_01__ETC___d231;
  tUWide DEF_IF_curReq_first__58_BITS_37_TO_34_98_EQ_15_01__ETC___d396;
  tUWide DEF_IF_curReq_first__58_BITS_37_TO_34_98_EQ_15_01__ETC___d226;
  tUWide DEF_IF_curReq_first__58_BITS_37_TO_34_98_EQ_15_01__ETC___d393;
  tUWide DEF_IF_curReq_first__58_BITS_37_TO_34_98_EQ_15_01__ETC___d221;
  tUWide DEF_IF_curReq_first__58_BITS_37_TO_34_98_EQ_15_01__ETC___d390;
  tUWide DEF_IF_curReq_first__58_BITS_37_TO_34_98_EQ_15_01__ETC___d216;
  tUWide DEF_IF_curReq_first__58_BITS_37_TO_34_98_EQ_15_01__ETC___d387;
  tUWide DEF_IF_curReq_first__58_BITS_37_TO_34_98_EQ_15_01__ETC___d211;
  tUWide DEF_SEL_ARR_memResp_first__40_BITS_31_TO_0_43_memR_ETC___d408;
  tUWide DEF_SEL_ARR_IF_bdata_serverAdapter_outData_ff_i_no_ETC___d316;
  tUWide DEF_getToMem__avValue1;
 
 /* Rules */
 public:
  void RL_bstate_serverAdapter_outData_enqueue();
  void RL_bstate_serverAdapter_outData_dequeue();
  void RL_bstate_serverAdapter_cnt_finalAdd();
  void RL_bstate_serverAdapter_s1__dreg_update();
  void RL_bstate_serverAdapter_stageReadResponseAlways();
  void RL_bstate_serverAdapter_moveToOutFIFO();
  void RL_bstate_serverAdapter_overRun();
  void RL_btag_serverAdapter_outData_enqueue();
  void RL_btag_serverAdapter_outData_dequeue();
  void RL_btag_serverAdapter_cnt_finalAdd();
  void RL_btag_serverAdapter_s1__dreg_update();
  void RL_btag_serverAdapter_stageReadResponseAlways();
  void RL_btag_serverAdapter_moveToOutFIFO();
  void RL_btag_serverAdapter_overRun();
  void RL_bdata_serverAdapter_outData_enqueue();
  void RL_bdata_serverAdapter_outData_dequeue();
  void RL_bdata_serverAdapter_cnt_finalAdd();
  void RL_bdata_serverAdapter_s1__dreg_update();
  void RL_bdata_serverAdapter_stageReadResponseAlways();
  void RL_bdata_serverAdapter_moveToOutFIFO();
  void RL_bdata_serverAdapter_overRun();
  void RL_checkHitMiss();
  void RL_sendMemoryRequest();
  void RL_readMemoryRequest();
 
 /* Methods */
 public:
  void METH_putFromProc(tUWide ARG_putFromProc_e);
  tUInt8 METH_RDY_putFromProc();
  tUWide METH_getToProc();
  tUInt8 METH_RDY_getToProc();
  tUWide METH_getToMem();
  tUInt8 METH_RDY_getToMem();
  void METH_putFromMem(tUWide ARG_putFromMem_e);
  tUInt8 METH_RDY_putFromMem();
 
 /* Reset routines */
 public:
  void reset_RST_N(tUInt8 ARG_rst_in);
 
 /* Static handles to reset routines */
 public:
 
 /* Pointers to reset fns in parent module for asserting output resets */
 private:
 
 /* Functions for the parent module to register its reset fns */
 public:
 
 /* Functions to set the elaborated clock id */
 public:
  void set_clk_0(char const *s);
 
 /* State dumping routine */
 public:
  void dump_state(unsigned int indent);
 
 /* VCD dumping routines */
 public:
  unsigned int dump_VCD_defs(unsigned int levels);
  void dump_VCD(tVCDDumpType dt, unsigned int levels, MOD_mkCache32_ins &backing);
  void vcd_defs(tVCDDumpType dt, MOD_mkCache32_ins &backing);
  void vcd_prims(tVCDDumpType dt, MOD_mkCache32_ins &backing);
};

#endif /* ifndef __mkCache32_ins_h__ */
