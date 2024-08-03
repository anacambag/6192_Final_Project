import FIFO::*;
import SpecialFIFOs::*;
import RegFile::*;
import RVUtil::*;
import Vector::*;
import KonataHelper::*;
import Printf::*;
import Ehr::*;
import SuperFIFO::*;
import Pipeline_functions::*;
import MemTypes::*;

typedef struct { Bit#(4) byte_en; Bit#(32) addr; Bit#(32) data; } Mem deriving (Eq, FShow, Bits);

interface RVIfc;
    method ActionValue#(Mem) getIReq();
    method Action getIResp(OneOrTwoWords a);
    method ActionValue#(Mem) getDReq();
    method Action getDResp(Mem a);
    method ActionValue#(Mem) getMMIOReq();
    method Action getMMIOResp(Mem a);
endinterface
typedef struct { Bool isUnsigned; Bit#(2) size; Bit#(2) offset; Bool mmio; } MemBusiness deriving (Eq, FShow, Bits);
typedef enum {
	Fetch, Decode, Execute, Writeback
} StateProc deriving (Eq, FShow, Bits); // ADDED THIS //

function Bool isMMIO(Bit#(32) addr);
    Bool x = case (addr) 
        32'hf000fff0: True;
        32'hf000fff4: True;
        32'hf000fff8: True;
        default: False;
    endcase;
    return x;
endfunction

typedef struct { Bit#(32) pc;
                 Bit#(32) ppc;
                 Bit#(1) epoch; 
                 KonataId k_id; // <- This is a unique identifier per instructions, for logging purposes
             } F2D deriving (Eq, FShow, Bits); 

typedef struct { 
    DecodedInst dinst;
    Bit#(32) pc;
    Bit#(32) ppc;
    Bit#(1) epoch;
    Bit#(32) rv1; 
    Bit#(32) rv2; 
    KonataId k_id; // <- This is a unique identifier per instructions, for logging purposes
    } D2E deriving (Eq, FShow, Bits);  

typedef struct { 
    MemBusiness mem_business;
    Bit#(32) data;
    DecodedInst dinst;
    KonataId k_id; // <- This is a unique identifier per instructions, for logging purposes
} E2W deriving (Eq, FShow, Bits);  

(* synthesize *)
module mkpipelined(RVIfc);
    // Interface with memory and devices
    FIFO#(Mem) toImem <- mkBypassFIFO;
    SuperFIFO#(Word) fromImem <- mkSuperFIFO;
    SuperFIFO#(Mem) toDmem <- mkSuperFIFO; //  CAMBIAMOS!!!!
    FIFO#(Mem) fromDmem <- mkBypassFIFO; // CAMBIAMOS!!
    SuperFIFO#(Mem) toMMIO <- mkSuperFIFO;// CAMBIAMOS!!!!!
    FIFO#(Mem) fromMMIO <- mkBypassFIFO; // CAMBIAMOS!!!!!

	// Code to support Konata visualization
    String dumpFile = "output.log" ;
    let lfh <- mkReg(InvalidFile);

	Reg#(KonataId) fresh_id <- mkReg(0);
	Reg#(KonataId) commit_id <- mkReg(0);

    Reg#(KonataId) fresh_id2 <- mkReg(1);
	Reg#(KonataId) commit_id2 <- mkReg(0);


	FIFO#(KonataId) retired <- mkFIFO;
	FIFO#(KonataId) squashed <- mkFIFO;

    FIFO#(KonataId) retired2 <- mkFIFO;
	FIFO#(KonataId) squashed2 <- mkFIFO;

    Ehr#(4, Bit#(32)) pc <- mkEhr(0);
    Vector#(32,Ehr#(2, Bit#(32))) bypass_val <- replicateM(mkEhr(0));

    // EhrReg#(Bit#(32)) pc <- mkReg(0);
    Ehr#(3, Bit#(1)) epoch <- mkEhr(0); // when is different in execute it will delete // 2 port EHR

   Vector#(32,Ehr#(3, Bit#(32))) rf <- replicateM(mkEhr(0)); // check this // 3 port EHR

    Vector#(32,Ehr#(6, Bit#(32))) scoreboard <- replicateM(mkEhr(0)); // would this be the correct implementation?

    Vector#(2,Ehr#(2, Bit#(1))) instruction_bool <- replicateM(mkEhr(1));


    SuperFIFO#(F2D) f2d <- mkSuperFIFO; 
    SuperFIFO#(D2E) d2e <- mkSuperFIFO;
    SuperFIFO#(E2W) e2w <- mkSuperFIFO;

    Reg#(Bool) fetch_flag <- mkReg(True);
    Reg#(Bool) decode_flag <- mkReg(False);
    Reg#(Bool) execute_flag <- mkReg(False);
    Reg#(Bool) writeback_flag <- mkReg(False);


    Reg#(StateProc) state <- mkReg(Fetch);
    Reg#(Bool) starting <- mkReg(True);
    // Reg#(Bool) decode1_done <- mkReg(False);

    Ehr#(2, Bit#(1)) decode1_done <- mkEhr(0);

    Ehr#(2, Bit#(1)) execute1_done <- mkEhr(0);

    Ehr#(2, Bit#(1)) isMemOrControlIns <- mkEhr(1);
    Ehr#(2, Bit#(1)) writeback_done <- mkEhr(0);

	rule do_tic_logging;
        if (starting) begin
            let f <- $fopen(dumpFile, "w") ;
            lfh <= f;
            $fwrite(f, "Kanata\t0004\nC=\t1\n");
            starting <= False;
        end
		konataTic(lfh);
	endrule
		
    rule fetch if (!starting); 
        
        Bit#(32) pc_fetched = pc[2]; 

        // 2 sequential instructions
        let numFetched = notLineBoundary(pc_fetched) ? 2 : 1;
     
        let iid <- nfetchKonata(lfh, fresh_id, 0, numFetched);


        labelKonataLeft(lfh, iid, $format("0x%x: ", pc_fetched));

        let req = Mem {byte_en : 0,
			   addr : pc_fetched,
			   data : 0}; // requesting in BRAM the instruction at given address

        f2d.enq1(F2D{pc: pc_fetched, ppc: pc_fetched+4, epoch: epoch[2], k_id: iid });
        
        if(notLineBoundary(pc_fetched)) begin

            f2d.enq2(F2D{pc: pc_fetched+4, ppc: pc_fetched+8, epoch: epoch[2], k_id: iid +1 });
            labelKonataLeft(lfh, iid+1, $format("0x%x: ", pc_fetched+4));
 
            pc[2] <= pc[2] +8; // added!! check final project
        end 

        else begin
            pc[2] <= pc[2] +4; 
        end

        toImem.enq(req); 

    endrule

    rule decode if (!starting);

        let resp = fromImem.first1();

        let instr = resp;
        let decodedInst = decodeInst(instr);

        let from_fetch = f2d.first1(); // borrar despues

   	
        decodeKonata(lfh, from_fetch.k_id);
        labelKonataLeft(lfh,from_fetch.k_id, $format("DASM(%x)", instr));

        let rs1_idx = getInstFields(instr).rs1; 
        let rs2_idx = getInstFields(instr).rs2;
        let rd_idx = getInstFields(instr).rd; 

		let rs1 = (rs1_idx ==0 ? 0 : rf[rs1_idx][2]); 
		let rs2 = (rs2_idx == 0 ? 0 : rf[rs2_idx][2]);

        if(scoreboard[rs1_idx][4] == 0 && scoreboard[rs2_idx][4] == 0)begin
 
            if (decodedInst.valid_rd && rd_idx !=0) begin
                scoreboard[rd_idx][4] <= scoreboard[rd_idx][4] + 1; 

            end

            d2e.enq1(D2E{dinst: decodedInst, pc: from_fetch.pc, ppc: from_fetch.ppc, epoch: from_fetch.epoch, rv1: rs1, rv2: rs2, k_id: from_fetch.k_id });
       
            f2d.deq1(); 

            decode1_done[0] <= 1; 

            fromImem.deq1();
            labelKonataLeft(lfh,from_fetch.k_id, $format("instruction 1"));

            if(isMemoryInst(decodedInst) || isControlInst(decodedInst)) begin

                instruction_bool[0][0] <= 0;
            
            end
        end

        else begin
            // STALL 
            labelKonataLeft(lfh,from_fetch.k_id, $format("instruction 1 stall"));
            // labelKonataLeft(lfh,from_fetch.k_id, $format(" rs1 idx: [%0d] content: (%x) ", rs1_idx, scoreboard[rs1_idx][4]));
            // labelKonataLeft(lfh,from_fetch.k_id,$format(" rs2 idx: [%0d] content: (%x) ", rs2_idx, scoreboard[rs2_idx][4]));
            decode1_done[0] <= 0;
        
        end
        
       
    endrule

    rule decode2 if (!starting && (decode1_done[1] == 1) && fromImem.deqReadyN(2) ); // chequear si asi se llama al notempty


        let resp = fromImem.first2();
        let instr = resp;
        let decodedInst = decodeInst(instr);

        let from_fetch = f2d.first2(); 
    
        decodeKonata(lfh, from_fetch.k_id);
        labelKonataLeft(lfh,from_fetch.k_id, $format("DASM(%x)", instr));
        // labelKonataLeft(lfh,from_fetch.k_id, $format("SB", instr));

        let rs1_idx = getInstFields(instr).rs1; 
        let rs2_idx = getInstFields(instr).rs2;
        let rd_idx = getInstFields(instr).rd; 

		let rs1 = (rs1_idx ==0 ? 0 : rf[rs1_idx][2]); 
		let rs2 = (rs2_idx == 0 ? 0 : rf[rs2_idx][2]);

    
        if(scoreboard[rs1_idx][5] == 0 && scoreboard[rs2_idx][5] == 0)begin
            
            if (decodedInst.valid_rd && rd_idx !=0) begin
                scoreboard[rd_idx][5] <= scoreboard[rd_idx][5] + 1; 
            end
  
            d2e.enq2(D2E{dinst: decodedInst, pc: from_fetch.pc, ppc: from_fetch.ppc, epoch: from_fetch.epoch, rv1: rs1, rv2: rs2, k_id: from_fetch.k_id });
       
            f2d.deq2(); 
            fromImem.deq2();
            decode1_done[1] <= 0;
            labelKonataLeft(lfh,from_fetch.k_id, $format("instruction 2"));

            if(isMemoryInst(decodedInst) || isControlInst(decodedInst)) begin

                instruction_bool[1][1] <= 0;
            
            end

            
        end
        else begin
            // STALL 
            labelKonataLeft(lfh,from_fetch.k_id, $format("instruction 2"));
            // labelKonataLeft(lfh,from_fetch.k_id, $format(" rs1 idx: [%0d] content: (%x) ", rs1_idx, scoreboard[rs1_idx][5]));
            // labelKonataLeft(lfh,from_fetch.k_id,$format(" rs2 idx: [%0d] content: (%x) ", rs2_idx,scoreboard[rs2_idx][5]));
        end
        

    endrule

    rule execute if (!starting);
        let from_decode = d2e.first1();
        d2e.deq1(); 
        labelKonataLeft(lfh,from_decode.k_id, $format("execute 1"));

        if (from_decode.epoch == epoch[0]) begin  // checking epoch value
            executeKonata(lfh, from_decode.k_id);
            let imm = getImmediate(from_decode.dinst);
            
            Bool mmio = False;

            let data = execALU32(from_decode.dinst.inst, from_decode.rv1, from_decode.rv2, imm, from_decode.pc); // would it be like this? Especially this: from_decode.dinst.inst
            let isUnsigned = 0;
   
            let funct3 = getInstFields(from_decode.dinst.inst).funct3;
            let size = funct3[1:0];
            let addr = from_decode.rv1 + imm;
            Bit#(2) offset = addr[1:0];
            if (isMemoryInst(from_decode.dinst)) begin
                // Technical details for load byte/halfword/word
                let shift_amount = {offset, 3'b0};
                let byte_en = 0;
                case (size) matches
                2'b00: byte_en = 4'b0001 << offset;
                2'b01: byte_en = 4'b0011 << offset;
                2'b10: byte_en = 4'b1111 << offset;
                endcase
                data = from_decode.rv2 << shift_amount;
                addr = {addr[31:2], 2'b0};
                isUnsigned = funct3[2];
                let type_mem = (from_decode.dinst.inst[5] == 1) ? byte_en : 0;
                let req = Mem {byte_en : type_mem,
                        addr : addr,
                        data : data};
                if (isMMIO(addr)) begin 
                    toMMIO.enq1(req);
                    labelKonataLeft(lfh,from_decode.k_id, $format(" (MMIO)", fshow(req)));
                    mmio = True;
                    end else begin
                    labelKonataLeft(lfh,from_decode.k_id, $format(" (MEM)", fshow(req)));
                    toDmem.enq1(req);
                end
            end
            else if (isControlInst(from_decode.dinst)) begin
                    data = from_decode.pc + 4; // relying on fetch pc+4
            end else begin 
                // labelKonataLeft(lfh,from_decode.k_id, $format(" (ALU)"));
            end
            let controlResult = execControl32(from_decode.dinst.inst, from_decode.rv1, from_decode.rv2, imm, from_decode.pc);
            let nextPc = controlResult.nextPC;

            // 1. This instruction is supposed to happen, but it guessed the next one wrong
            // 2. This instruction is not supposed to happen
            if(from_decode.ppc != nextPc) begin // MISS PREDICTION!!!
                epoch[0] <= epoch[0] + 1;
                pc[0] <= nextPc;
                labelKonataLeft(lfh,from_decode.k_id, $format("Thinks this mispredicts the next"));
                // flush the pipeline or handle the mispredicted instructions.

                
            end

            let mem_bus = MemBusiness { isUnsigned : unpack(isUnsigned), size : size, offset : offset, mmio: mmio}; // CHECK IF THIS IS VALID OR NEEDS TO BE IN DIF CYCLES
            e2w.enq1(E2W{mem_business: mem_bus, data: data, dinst: from_decode.dinst, k_id: from_decode.k_id });
            // execute1_done[0] <= 1;
      
        end

        else begin // SQUASH INSTRUCTION. EPOCH DID NOT MATCH SO WE DO NOT WANT THIS INSTRUCTION
            squashed.enq(from_decode.k_id);
            if (from_decode.dinst.valid_rd && getInstFields(from_decode.dinst.inst).rd != 0) begin
                scoreboard[getInstFields(from_decode.dinst.inst).rd][2] <= scoreboard[getInstFields(from_decode.dinst.inst).rd][2] - 1;
            end 

        end

        

    endrule

    rule execute2 if (!starting  && (instruction_bool[1][0]==1) && (instruction_bool[1][1]==1));
        let from_decode = d2e.first2();
        d2e.deq2(); 

        labelKonataLeft(lfh,from_decode.k_id, $format("execute 2"));
        if (from_decode.epoch == epoch[1]) begin  // checking epoch value
            executeKonata(lfh, from_decode.k_id);
            let imm = getImmediate(from_decode.dinst);
            
            Bool mmio = False;

            let data = execALU32(from_decode.dinst.inst, from_decode.rv1, from_decode.rv2, imm, from_decode.pc); // would it be like this? Especially this: from_decode.dinst.inst
            let isUnsigned = 0;
   
            let funct3 = getInstFields(from_decode.dinst.inst).funct3;
            let size = funct3[1:0];
            let addr = from_decode.rv1 + imm;
            Bit#(2) offset = addr[1:0];
            if (isMemoryInst(from_decode.dinst)) begin
                // Technical details for load byte/halfword/word
                let shift_amount = {offset, 3'b0};
                let byte_en = 0;
                case (size) matches
                2'b00: byte_en = 4'b0001 << offset;
                2'b01: byte_en = 4'b0011 << offset;
                2'b10: byte_en = 4'b1111 << offset;
                endcase
                data = from_decode.rv2 << shift_amount;
                addr = {addr[31:2], 2'b0};
                isUnsigned = funct3[2];
                let type_mem = (from_decode.dinst.inst[5] == 1) ? byte_en : 0;
                let req = Mem {byte_en : type_mem,
                        addr : addr,
                        data : data};
                // HASTA AQUI TODO BIEN

                if (isMMIO(addr)) begin 
                    toMMIO.enq2(req); // ESTO ES UNO DE BLOCKING

                    labelKonataLeft(lfh,from_decode.k_id, $format(" (MMIO)", fshow(req)));
                    mmio = True;
                end else begin
                    labelKonataLeft(lfh,from_decode.k_id, $format(" (MEM)", fshow(req)));
                    toDmem.enq2(req); // ESTO ES UNO DE BLOCKING
                end
            end
            else if (isControlInst(from_decode.dinst)) begin
                    data = from_decode.pc + 4; // relying on fetch pc+4
            end
             else begin 
                // labelKonataLeft(lfh,from_decode.k_id, $format(" (ALU)"));
            end
            let controlResult = execControl32(from_decode.dinst.inst, from_decode.rv1, from_decode.rv2, imm, from_decode.pc);
            let nextPc = controlResult.nextPC;

            // 1. This instruction is supposed to happen, but it guessed the next one wrong
            // 2. This instruction is not supposed to happen

            if(from_decode.ppc != nextPc) begin // MISS PREDICTION!!!
                epoch[1] <= epoch[1] + 1; // ESTO ES UNO DE BLOCKING
                pc[1] <= nextPc; // ESTO ES UNO DE BLOCKING
                labelKonataLeft(lfh,from_decode.k_id, $format("Thinks this mispredicts the next"));
                // flush the pipeline or handle the mispredicted instructions.
 
            end

            let mem_bus = MemBusiness { isUnsigned : unpack(isUnsigned), size : size, offset : offset, mmio: mmio}; // CHECK IF THIS IS VALID OR NEEDS TO BE IN DIF CYCLES
            e2w.enq2(E2W{mem_business: mem_bus, data: data, dinst: from_decode.dinst, k_id: from_decode.k_id });
            
        end

        else begin // SQUASH INSTRUCTION. EPOCH DID NOT MATCH SO WE DO NOT WANT THIS INSTRUCTION
            squashed2.enq(from_decode.k_id); // NO DA PROBLEMA
            if (from_decode.dinst.valid_rd && getInstFields(from_decode.dinst.inst).rd != 0) begin
                 scoreboard[getInstFields(from_decode.dinst.inst).rd][3] <= scoreboard[getInstFields(from_decode.dinst.inst).rd][3] - 1; // ESTO ES UNO DE BLOCKING
            end 
        end

        

    endrule

    

    rule writeback if (!starting);
        let from_execute = e2w.first1();
        e2w.deq1();
        writebackKonata(lfh,from_execute.k_id);
        retired.enq(from_execute.k_id);

        let data = from_execute.data;
        let fields = getInstFields(from_execute.dinst.inst);
        labelKonataLeft(lfh,from_execute.k_id, $format("WRITEBACK 1"));

        if(!isMemoryInst(from_execute.dinst) && !isControlInst(from_execute.dinst)) begin
            isMemOrControlIns[0] <= 0;
        end

        if (isMemoryInst(from_execute.dinst)) begin 

            let resp = ?;
		    if (from_execute.mem_business.mmio) begin 
                resp = fromMMIO.first();
		        fromMMIO.deq();
		    end else begin 
                resp = fromDmem.first();
		        fromDmem.deq();
		    end
            let mem_data = resp.data;
            mem_data = mem_data >> {from_execute.mem_business.offset ,3'b0};
            case ({pack(from_execute.mem_business.isUnsigned), from_execute.mem_business.size}) matches
	     	3'b000 : data = signExtend(mem_data[7:0]);
	     	3'b001 : data = signExtend(mem_data[15:0]);
	     	3'b100 : data = zeroExtend(mem_data[7:0]);
	     	3'b101 : data = zeroExtend(mem_data[15:0]);
	     	3'b010 : data = mem_data;
             endcase
		end


		if (from_execute.dinst.valid_rd) begin
            let rd_idx = fields.rd;
            if (from_execute.dinst.valid_rd && rd_idx != 0) begin
                scoreboard[rd_idx][0] <= scoreboard[rd_idx][0] - 1; 
            end
            if (rd_idx != 0) begin rf[rd_idx][0] <=data; end 
		end


	endrule


    rule writeback2 if (!starting && isMemOrControlIns[1] == 0);
        let from_execute = e2w.first2();
        labelKonataLeft(lfh,from_execute.k_id, $format("WRITEBACK 2"));
        // if (isMemoryInst(from_execute.dinst)) begin 
        //     //STALL
		// end

            e2w.deq2();
            writebackKonata(lfh,from_execute.k_id);
            retired2.enq(from_execute.k_id);

            let data = from_execute.data;
            let fields = getInstFields(from_execute.dinst.inst);

            if (from_execute.dinst.valid_rd) begin
                let rd_idx = fields.rd;
                if (rd_idx != 0) begin
                    scoreboard[rd_idx][1] <= scoreboard[rd_idx][1] - 1; // ADDED THIS
                end
                if (rd_idx != 0) begin rf[rd_idx][1] <=data; end // CHANGED THIS SO THAT RF USES EHR
            end
            


	endrule

    rule settingMemory;

        isMemOrControlIns[1] <= 1;

    endrule
		

	// ADMINISTRATION:

    rule administrative_konata_commit;
		    retired.deq();
		    let f = retired.first();
		    commitKonata(lfh, f, commit_id);
	endrule
		
	rule administrative_konata_flush;
		    squashed.deq();
		    let f = squashed.first();
		    squashKonata(lfh, f);
	endrule

    rule administrative_konata_commit2;
        retired2.deq();
        let f = retired2.first();
        commitKonata(lfh, f, commit_id);
    endrule
    
    rule administrative_konata_flush_2;
        squashed2.deq();
        let f = squashed2.first();
        squashKonata(lfh, f);
    endrule
		
    method ActionValue#(Mem) getIReq();
		toImem.deq(); // DEQUEING DE 1 MAYBE 
		return toImem.first(); // 
    endmethod
    method Action getIResp(OneOrTwoWords a);
        // fromImem superscalar enq1 enq2 depending if validity
        fromImem.enq1(a.ins1);

        if (isValid(a.ins2)) begin
            fromImem.enq2(fromMaybe(?,a.ins2));
        end

    endmethod
    method ActionValue#(Mem) getDReq();
		toDmem.deq1();
		return toDmem.first1();
    endmethod
    method Action getDResp(Mem a);
		fromDmem.enq(a);
    endmethod
    method ActionValue#(Mem) getMMIOReq();
		toMMIO.deq1();
		return toMMIO.first1();
    endmethod
    method Action getMMIOResp(Mem a);
		fromMMIO.enq(a);
    endmethod
endmodule
