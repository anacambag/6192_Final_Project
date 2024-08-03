import FIFOF::*;
import SpecialFIFOs::*;
import Ehr::*;
import Vector::*;

interface SuperFIFO#(type t);
    method Action enq1(t x);
    method Action enq2(t x);
    method Bool enqReadyN(Bit#(2) n);  // valid 1 or 2
    method Bool deqReadyN(Bit#(2) n);  // valid 1 or 2
    method Action deq1;
    method Action deq2;
    method t first1;
    method t first2;
endinterface

module mkSuperFIFO(SuperFIFO#(t)) provisos (Bits#(t,tSz), Eq#(t));
    Ehr#(2, Bit#(1)) enqueueFIFO <- mkEhr(unpack(0));
    Ehr#(2, Bit#(1)) dequeueFIFO <- mkEhr(unpack(0));

    Vector#(2, FIFOF#(t)) internalFIFOs <- replicateM(mkFIFOF);

    Bit#(1) fifoIdxEnq1 = enqueueFIFO[0];
    Bit#(1) fifoIdxEnq2 = enqueueFIFO[0] + 1;
    Bool can_enq1 = internalFIFOs[fifoIdxEnq1].notFull;
    Bool can_enq2 = internalFIFOs[fifoIdxEnq2].notFull;
    
    Bit#(1) fifoIdxDeq1 = dequeueFIFO[0];
    Bit#(1) fifoIdxDeq2 = dequeueFIFO[0] + 1;
    Bool can_deq1 = internalFIFOs[fifoIdxDeq1].notEmpty;
    Bool can_deq2 = internalFIFOs[fifoIdxDeq2].notEmpty;

    Ehr#(2, Maybe#(t)) want_enq1 <- mkEhr(tagged Invalid);
    Ehr#(2, Maybe#(t)) want_enq2 <- mkEhr(tagged Invalid);
    Ehr#(2, Bool) want_deq1 <- mkEhr(False);
    Ehr#(2, Bool) want_deq2 <- mkEhr(False);

    rule canonicalize;
        if (want_enq1[1] matches tagged Valid .el) begin
            enqueueFIFO[0] <= enqueueFIFO[0]+1;
            internalFIFOs[fifoIdxEnq1].enq(el);
        end
        if (want_deq1[1]) begin
            dequeueFIFO[0] <= dequeueFIFO[0] + 1;
            internalFIFOs[fifoIdxDeq1].deq;
        end
        want_enq1[1] <= tagged Invalid;
        want_deq1[1] <= False;
  
        if (want_enq2[1] matches tagged Valid .el) begin
            enqueueFIFO[1] <= enqueueFIFO[1]+1;
            internalFIFOs[fifoIdxEnq2].enq(el);
        end
        if (want_deq2[1]) begin
            dequeueFIFO[1] <= dequeueFIFO[1] + 1;
            internalFIFOs[fifoIdxDeq2].deq;
        end
        want_enq2[1] <= tagged Invalid;
        want_deq2[1] <= False;
    endrule

    method Action enq1(t x) if (want_enq1[0] == tagged Invalid && can_enq1);
        want_enq1[0] <= Valid(x);
	endmethod

    method Action enq2(t x) if (want_enq2[0] == tagged Invalid && can_enq2);
        want_enq2[0] <= Valid(x);
    endmethod


    method Bool enqReadyN(Bit#(2) n);  // valid 1 or 2
    return case (n) matches
        0: False;
        1: (can_enq1 || can_enq2);
        2: (can_enq1 && can_enq2);
        default: False;
    endcase;
    endmethod 

    method Bool deqReadyN(Bit#(2) n);  // valid 1 or 2
    return case (n) matches
        0: False;
        1: (can_deq1 || can_deq2);
        2: (can_deq1 && can_deq2);
        default: False;
    endcase;
    endmethod 

    method t first1();
        return internalFIFOs[fifoIdxDeq1].first;
    endmethod

    method t first2();
        return internalFIFOs[fifoIdxDeq2].first;
    endmethod

    method Action deq1 if(can_deq1 && !want_deq1[0]);
        want_deq1[0] <= True;
    endmethod

    method Action deq2 if(can_deq2 && !want_deq2[0]);
        want_deq2[0] <= True;
    endmethod
endmodule

module mkBypassSuperFIFO(SuperFIFO#(t)) provisos (Bits#(t,tSz), Eq#(t));
    // TODO: This was barely tested
    Ehr#(2, Bit#(1)) enqueueFIFO <- mkEhr(unpack(0));
    Ehr#(2, Bit#(1)) dequeueFIFO <- mkEhr(unpack(0));

    Vector#(2, FIFOF#(t)) internalFIFOs <- replicateM(mkUGFIFOF);

    Bit#(1) fifoIdxEnq1 = enqueueFIFO[0];
    Bit#(1) fifoIdxEnq2 = enqueueFIFO[0] + 1;
    Bool can_enq1 = internalFIFOs[fifoIdxEnq1].notFull;
    Bool can_enq2 = internalFIFOs[fifoIdxEnq2].notFull;
    
    Bit#(1) fifoIdxDeq1 = dequeueFIFO[0];
    Bit#(1) fifoIdxDeq2 = dequeueFIFO[0] + 1;
    Bool can_deq1 = internalFIFOs[fifoIdxDeq1].notEmpty;
    Bool can_deq2 = internalFIFOs[fifoIdxDeq2].notEmpty;

    Ehr#(2, Maybe#(t)) want_enq1 <- mkEhr(tagged Invalid);
    Ehr#(2, Maybe#(t)) want_enq2 <- mkEhr(tagged Invalid);
    Ehr#(2, Bool) want_deq1 <- mkEhr(False);
    Ehr#(2, Bool) want_deq2 <- mkEhr(False);

    (* fire_when_enabled, no_implicit_conditions *)
    rule canonicalize;
        if (want_enq1[1] matches tagged Valid .el) begin
            enqueueFIFO[0] <= enqueueFIFO[0]+1;
            internalFIFOs[fifoIdxEnq1].enq(el);
        end
        if (want_deq1[1]) begin
            dequeueFIFO[0] <= dequeueFIFO[0] + 1;
            internalFIFOs[fifoIdxDeq1].deq;
        end
        want_enq1[1] <= tagged Invalid;
        want_deq1[1] <= False;
  
        if (want_enq2[1] matches tagged Valid .el) begin
            enqueueFIFO[1] <= enqueueFIFO[1]+1;
            internalFIFOs[fifoIdxEnq2].enq(el);
        end
        if (want_deq2[1]) begin
            dequeueFIFO[1] <= dequeueFIFO[1] + 1;
            internalFIFOs[fifoIdxDeq2].deq;
        end
        want_enq2[1] <= tagged Invalid;
        want_deq2[1] <= False;
    endrule

    method Action enq1(t x) if (want_enq1[0] == tagged Invalid && can_enq1);
        want_enq1[0] <= Valid(x);
	endmethod

    method Action enq2(t x) if (want_enq2[0] == tagged Invalid && can_enq2);
        want_enq2[0] <= Valid(x);
    endmethod

    
    method Bool enqReadyN(Bit#(2) n);  // valid 1 or 2
    return case (n) matches
        0: False;
        1: (can_enq1 || can_enq2);
        2: (can_enq1 && can_enq2);
        default: False;
    endcase;
    endmethod 

    method Bool deqReadyN(Bit#(2) n);  // valid 1 or 2
    return case (n) matches
        0: False;
        1: (can_deq1 || can_deq2);
        2: (can_deq1 && can_deq2);
        default: False;
    endcase;
    endmethod 

    method t first1() if ((can_deq1 || want_enq1[1] != tagged Invalid));
        if (can_deq1) return internalFIFOs[fifoIdxDeq1].first;
        else begin if (want_enq1[1] matches tagged Valid .x) return x;
        else return ?;
    end
    endmethod

    method t first2() if ((can_deq2 || want_enq2[1] != tagged Invalid));
        if (can_deq2) return internalFIFOs[fifoIdxDeq2].first;
        else begin if (want_enq2[1] matches tagged Valid .x) return x;
        else return ?;
        end
    endmethod

    method Action deq1 if((want_enq1[1] != tagged Invalid || can_deq1) && !want_deq1[0] );
        want_deq1[0] <= True;
    endmethod

    method Action deq2 if((want_enq2[1] != tagged Invalid || can_deq2) && !want_deq2[0]);
        want_deq2[0] <= True;
    endmethod
endmodule

