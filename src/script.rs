use crate::u256::U256;
use crate::sha256::Sha256;
use crate::sha256::HMAC;
use crate::ripemd160::Ripemd160;

// Bitcoin Script Interpreter with Variable-Length Handling 
// Opcode definitions 
// Constants
const OP_0: u8 = 0x00;
// 0x01-0x4b The next opcode bytes is data to be pushed onto the stack
const OP_PUSHDATA1: u8 = 0x4c;
const OP_PUSHDATA2: u8 = 0x4d;
const OP_PUSHDATA4: u8 = 0x4e;
const OP_1NEGATE: u8 = 0x4f;
const OP_1: u8 = 0x51;
const OP_2: u8 = 0x52;
const OP_3: u8 = 0x53;
const OP_4: u8 = 0x54;
const OP_5: u8 = 0x55;
const OP_6: u8 = 0x56;
const OP_7: u8 = 0x57;
const OP_8: u8 = 0x58;
const OP_9: u8 = 0x59;
const OP_10: u8 = 0x5a;
const OP_11: u8 = 0x5b;
const OP_12: u8 = 0x5c;
const OP_13: u8 = 0x5d;
const OP_14: u8 = 0x5e;
const OP_15: u8 = 0x5f;
const OP_16: u8 = 0x60;
// Flow control
const OP_NOP: u8 = 0x61;
const OP_IF: u8 = 0x63;
const OP_NOTIF: u8 = 0x64;
const OP_ELSE: u8 = 0x67;
const OP_ENDIF: u8 = 0x68;
const OP_VERIFY: u8 = 0x69;
const OP_RETURN: u8 = 0x6a;
// Stack
const OP_TOALTSTACK: u8 = 0x6b;
const OP_FROMALTSTACK: u8 = 0x6c;
const OP_IFDUP: u8 = 0x73;
const OP_DEPTH: u8 = 0x74;
const OP_DROP: u8 = 0x75;
const OP_DUP: u8 = 0x76;
const OP_NIP: u8 = 0x77;
const OP_OVER: u8 = 0x78;
const OP_PICK: u8 = 0x79;
const OP_ROLL: u8 = 0x7a;
const OP_ROT: u8 = 0x7b;
const OP_SWAP: u8 = 0x7c;
const OP_TUCK: u8 = 0x7d;
const OP_2DROP: u8 = 0x6d;
const OP_2DUP: u8 = 0x6e;
const OP_3DUP: u8 = 0x6f;
const OP_2OVER: u8 = 0x70;
const OP_2ROT: u8 = 0x71;
const OP_2SWAP: u8 = 0x72;
// Splice
const OP_CAT: u8 = 0x7e;
const OP_SUBSTR: u8 = 0x7f;
const OP_LEFT: u8 = 0x80;
const OP_RIGHT: u8 = 0x81;
const OP_SIZE: u8 = 0x82;
// Bitwise logic
const OP_INVERT: u8 = 0x83;
const OP_AND: u8 = 0x84;
const OP_OR: u8 = 0x85;
const OP_XOR: u8 = 0x86;
const OP_EQUAL: u8 = 0x87;
const OP_EQUALVERIFY: u8 = 0x88;
// Arithmetic
const OP_1ADD: u8 = 0x8b;
const OP_1SUB: u8 = 0x8c;
const OP_2MUL: u8 = 0x8d;
const OP_2DIV: u8 = 0x8e;
const OP_NEGATE: u8 = 0x8f;
const OP_ABS: u8 = 0x90;
const OP_NOT: u8 = 0x91;
const OP_0NOTEQUAL: u8 = 0x92;
const OP_ADD: u8 = 0x93;
const OP_SUB: u8 = 0x94;
const OP_MUL: u8 = 0x95;
const OP_DIV: u8 = 0x96;
const OP_MOD: u8 = 0x97;
const OP_LSHIFT: u8 = 0x98;
const OP_RSHIFT: u8 = 0x99;
const OP_BOOLAND: u8 = 0x9a;
const OP_BOOLOR: u8 = 0x9b;
const OP_NUMEQUAL: u8 = 0x9c;
const OP_NUMEQUALVERIFY: u8 = 0x9d;
const OP_NUMNOTEQUAL: u8 = 0x9e;
const OP_LESSTHAN: u8 = 0x9f;
const OP_GREATERTHAN: u8 = 0xa0;
const OP_LESSTHANOREQUAL: u8 = 0xa1;
const OP_GREATERTHANOREQUAL: u8 = 0xa2;
const OP_MIN: u8 = 0xa3;
const OP_MAX: u8 = 0xa4;
const OP_WITHIN: u8 = 0xa5;
// Crypto
const OP_RIPEMD160: u8 = 0xa6;
const OP_SHA1: u8 = 0xa7;
const OP_SHA256: u8 = 0xa8;
const OP_HASH160: u8 = 0xa9;
const OP_HASH256: u8 = 0xaa;
const OP_CODESEPARATOR: u8 = 0xab;
const OP_CHECKSIG: u8 = 0xac;
const OP_CHECKSIGVERIFY: u8 = 0xad;
const OP_CHECKMULTISIG: u8 = 0xae;
const OP_CHECKMULTISIGVERIFY: u8 = 0xaf;
const OP_CHECKSIGADD: u8 = 0xba;
// Locktime
const OP_CHECKLOCKTIMEVERIFY: u8 = 0xb1; //  (previously OP_NOP2)
const OP_CHECKSEQUENCEVERIFY: u8 = 0xb2; //  (previously OP_NOP3)
// Pseudo-words
const OP_PUBKEYHASH: u8 = 0xfd;
const OP_PUBKEY: u8 = 0xfe;
const OP_INVALIDOPCODE: u8 = 0xff;
// Reserved words
const OP_RESERVED: u8 = 0x50;
const OP_VER: u8 = 0x62;
const OP_VERIF: u8 = 0x65;
const OP_VERNOTIF: u8 = 0x66;
const OP_RESERVED1: u8 = 0x89;
const OP_RESERVED2: u8 = 0x8a;
const OP_NOP1: u8 = 0xb0;
const OP_NOP4: u8 = 0xb3;
const OP_NOP5: u8 = 0xb4;
const OP_NOP6: u8 = 0xb5;
const OP_NOP7: u8 = 0xb6;
const OP_NOP8: u8 = 0xb7;
const OP_NOP9: u8 = 0xb8;
const OP_NOP10: u8 = 0xb9;
type OpFunction = fn(&mut Vec<&[u8]>, &mut usize, script: &[u8]) -> Result<(), &'static str>;

// Dummy cryptographic functions (replace with real implementations) 
fn sha256ripemd160(data: &[u8]) -> Vec { 
    // Implement your own SHA256 and RIPEMD160 functions or use external libraries for them. 
    // This example is simplified and does not include actual cryptographic functions. 
    // Use a proven cryptographic library for production code. 
    data.to_vec() 
} 

fn create_function_array() -> [OpFunction; 256] {
    let default_function = |stack: &mut Vec<&[u8]>, script_cursor: &mut usize, script: &[u8]| -> Result<(), &'static str> {
        Ok(())
    };
    let mut function_array: [OpFunction; 256] = [default_function; 256];

    function_array[OP_DUP] = |stack: &mut Vec<&[u8]>, script_cursor: &mut usize, script: &[u8]| -> Result<(), &'static str> {
        if let Some(item) = stack.last().cloned() {
            stack.push(item); 
        } else {
            return Err("OP_DUP failed"); 
        }
        *script_cursor += 1;
        Ok(())
    };

    function_array[OP_HASH160] = |stack: &mut Vec<&[u8]>, script_cursor: &mut usize, script: &[u8]| -> Result<(), &'static str> {
        if let Some(item) = stack.pop() {
            let hashed_item = sha256ripemd160(&item); 
            stack.push(hashed_item); 
        } else {
            return Err("OP_HASH160 failed"); 
        } 
        *script_cursor += 1;
        Ok(())
    };

    function_array[OP_EQUALVERIFY] = |stack: &mut Vec<&[u8]>, script_cursor: &mut usize, script: &[u8]| -> Result<(), &'static str> {
        if let (Some(item1), Some(item2)) = (stack.pop(), stack.pop()) {
            if item1 == item2 {
                // Verification successful, do nothing 
            } else {
                return Err("OP_EQUALVERIFY failed"); 
            } 
        } else { 
            return Err("OP_EQUALVERIFY failed"); 
        } 
        *script_cursor += 1;
        Ok(())
    };

    for opcode in 1..0x4c {
        function_array[opcode] = |stack: &mut Vec<&[u8]>, script_cursor: &mut usize, script: &[u8]| -> Result<(), &'static str> {
            let data_length = opcode as usize; 
            let data_start = *script_cursor + 1; 
            let data_end = data_start + data_length; 
            if data_end > script.len() { 
                return Err("Variable-length data exceeds script length"); 
            }
            let data = script[data_start..data_end].to_vec(); 
            stack.push(data); 
            *script_cursor = data_end;
            *script_cursor += 1;
            Ok(())
        };
    }
    function_array
}

// Bitcoin Script interpreter function with variable-length handling 
fn run_script(script: &[u8]) -> Result<(), &'static str> {
    let op_function_array = create_function_array();
    let mut stack: Vec<&[u8]> = Vec::new();
    let mut script_cursor = 0; 
    while script_cursor < script.len() { 
        let opcode = script[script_cursor]; 
        let result = op_function_array[opcode](&mut stack, &mut script_cursor, script);
        if !result.is_ok() {
            return result
        }
    } 
    Ok(()) 
} 
fn main() {
    // Example P2PKH Bitcoin Script with variable-length data 
    let bitcoin_script_hex = "76a914010101010101010101010101010101010101010188ac"; 
    let bitcoin_script_bytes = hex::decode(bitcoin_script_hex).expect("Invalid hex string"); 
    // Run the Bitcoin Script
    match run_script(&bitcoin_script_bytes) {
        Ok(_) => println!("Script execution successful!"), 
        Err(err) => println!("Script execution failed: {}", err), 
    } 
}
