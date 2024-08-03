import FIFO::*;
import SpecialFIFOs::*;
import RegFile::*;
import RVUtil::*;
import Vector::*;
import KonataHelper::*;
import Printf::*;
import Ehr::*;
import MemTypes::*;

interface AddrPred;
    method Addr nap(Addr pc);
    method Action update(Addr pc, Addr nextPC,Bool taken);
endinterface


module mkBTB(AddrPred);

    method Action update(Addr pc, Addr nextPC,Bool taken);

    endmethod


    method Addr nap(Addr pc);

    endmethod 

endmodule

