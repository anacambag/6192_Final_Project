import MemTypes::*;

function Bool notLineBoundary(Bit#(32) pcf);
    Bool check_line;

    let offset = parseAddress(pcf).offset;

    if (offset == ~0) begin
        check_line = False;  // on a boundary
    end
    else begin
        check_line = True;
    end

    return check_line;
endfunction