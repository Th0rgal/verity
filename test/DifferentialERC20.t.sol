// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import {Test, console2} from "forge-std/Test.sol";
import "./DiffTestConfig.sol";
import "./DifferentialTestBase.sol";

contract ERC20DiffModel {
    uint256 private constant MAX_UINT256 = type(uint256).max;

    address private _owner;
    uint256 private _totalSupply;
    mapping(address => uint256) private _balances;
    mapping(address => mapping(address => uint256)) private _allowances;

    constructor(address initialOwner) {
        _owner = initialOwner;
        _totalSupply = 0;
    }

    function mint(address to, uint256 amount) external {
        require(msg.sender == _owner, "Caller is not the owner");
        _balances[to] += amount;
        _totalSupply += amount;
    }

    function transfer(address to, uint256 amount) external {
        uint256 senderBal = _balances[msg.sender];
        require(senderBal >= amount, "Insufficient balance");

        if (msg.sender == to) return;

        _balances[msg.sender] = senderBal - amount;
        _balances[to] += amount;
    }

    function approve(address spender, uint256 amount) external {
        _allowances[msg.sender][spender] = amount;
    }

    function transferFrom(address fromAddr, address to, uint256 amount) external {
        uint256 currentAllowance = _allowances[fromAddr][msg.sender];
        require(currentAllowance >= amount, "Insufficient allowance");

        uint256 fromBalance = _balances[fromAddr];
        require(fromBalance >= amount, "Insufficient balance");

        if (fromAddr != to) {
            _balances[fromAddr] = fromBalance - amount;
            _balances[to] += amount;
        }

        if (currentAllowance != MAX_UINT256) {
            _allowances[fromAddr][msg.sender] = currentAllowance - amount;
        }
    }

    function balanceOf(address addr) external view returns (uint256) {
        return _balances[addr];
    }

    function allowanceOf(address ownerAddr, address spender) external view returns (uint256) {
        return _allowances[ownerAddr][spender];
    }

    function totalSupply() external view returns (uint256) {
        return _totalSupply;
    }

    function owner() external view returns (address) {
        return _owner;
    }
}

contract DifferentialERC20 is DiffTestConfig, DifferentialTestBase {
    ERC20DiffModel private token;

    mapping(address => uint256) private edslBalances; // slot 2
    mapping(address => mapping(address => uint256)) private edslAllowances; // slot 3
    mapping(uint256 => uint256) private edslStorage; // slot 1 => totalSupply
    mapping(uint256 => address) private edslStorageAddr; // slot 0 => owner

    function setUp() public {
        token = new ERC20DiffModel(address(this));
        edslStorage[1] = 0;
        edslStorageAddr[0] = address(this);
    }

    function _runInterpreter(
        string memory functionName,
        address sender,
        address arg0,
        address arg1,
        uint256 arg2,
        string memory mapState,
        string memory map2State
    ) internal returns (string memory) {
        string[] memory inputs = new string[](3);
        inputs[0] = "bash";
        inputs[1] = "-c";

        bytes32 functionSig = keccak256(bytes(functionName));
        string memory argsStr = "";

        if (
            functionSig == keccak256(bytes("mint"))
                || functionSig == keccak256(bytes("transfer"))
                || functionSig == keccak256(bytes("approve"))
        ) {
            argsStr = string.concat(vm.toString(uint256(uint160(arg0))), " ", vm.toString(arg2));
        } else if (functionSig == keccak256(bytes("transferFrom"))) {
            argsStr = string.concat(
                vm.toString(uint256(uint160(arg0))),
                " ",
                vm.toString(uint256(uint160(arg1))),
                " ",
                vm.toString(arg2)
            );
        } else if (functionSig == keccak256(bytes("balanceOf"))) {
            argsStr = vm.toString(uint256(uint160(arg0)));
        } else if (functionSig == keccak256(bytes("allowanceOf"))) {
            argsStr = string.concat(vm.toString(uint256(uint160(arg0))), " ", vm.toString(uint256(uint160(arg1))));
        }

        string memory storageStr = string.concat("storage=1:", vm.toString(edslStorage[1]));
        string memory addrStr = string.concat("addr=0:", _addressToString(edslStorageAddr[0]));
        string memory mapStr = bytes(mapState).length > 0 ? string.concat(" map=\"", mapState, "\"") : "";
        string memory map2Str = bytes(map2State).length > 0 ? string.concat(" map2=\"", map2State, "\"") : "";

        inputs[2] = string.concat(
            _interpreterPreamble(),
            " ERC20 ",
            functionName,
            " ",
            _addressToString(sender),
            bytes(argsStr).length > 0 ? string.concat(" ", argsStr) : "",
            " ",
            storageStr,
            " ",
            addrStr,
            mapStr,
            map2Str,
            " value=0 timestamp=",
            vm.toString(block.timestamp)
        );

        return string(vm.ffi(inputs));
    }

    function _buildMapState(address a, address b, address c) internal view returns (string memory) {
        address[3] memory keys = [a, b, c];
        string memory out = "";
        bool first = true;

        for (uint256 i = 0; i < keys.length; i++) {
            address k = keys[i];
            bool seen = false;
            for (uint256 j = 0; j < i; j++) {
                if (keys[j] == k) {
                    seen = true;
                    break;
                }
            }
            if (seen || edslBalances[k] == 0) continue;
            if (!first) out = string.concat(out, ",");
            out = string.concat(out, "2:", _toLowerCase(vm.toString(k)), ":", vm.toString(edslBalances[k]));
            first = false;
        }

        return out;
    }

    function _buildMap2State(address ownerAddr, address spenderA, address spenderB) internal view returns (string memory) {
        string memory out = "";
        bool first = true;

        uint256 valA = edslAllowances[ownerAddr][spenderA];
        if (valA > 0) {
            out = string.concat(
                "3:",
                _toLowerCase(vm.toString(ownerAddr)),
                ":",
                _toLowerCase(vm.toString(spenderA)),
                ":",
                vm.toString(valA)
            );
            first = false;
        }

        if (spenderB != spenderA) {
            uint256 valB = edslAllowances[ownerAddr][spenderB];
            if (valB > 0) {
                if (!first) out = string.concat(out, ",");
                out = string.concat(
                    out,
                    "3:",
                    _toLowerCase(vm.toString(ownerAddr)),
                    ":",
                    _toLowerCase(vm.toString(spenderB)),
                    ":",
                    vm.toString(valB)
                );
            }
        }

        return out;
    }

    function _updateStateFromEDSL(
        string memory edslResult,
        address sender,
        address arg0,
        address arg1
    ) internal {
        (bool hasSupply, uint256 supplyVal) = _extractStorageChange(edslResult, 1);
        if (hasSupply) edslStorage[1] = supplyVal;

        (bool hasOwner, uint256 ownerNat) = _extractStorageAddrChange(edslResult, 0);
        if (hasOwner) edslStorageAddr[0] = address(uint160(ownerNat));

        (bool senderChanged, uint256 senderBal) = _extractMappingChange(edslResult, 2, sender);
        if (senderChanged) edslBalances[sender] = senderBal;
        (bool arg0Changed, uint256 arg0Bal) = _extractMappingChange(edslResult, 2, arg0);
        if (arg0Changed) edslBalances[arg0] = arg0Bal;
        (bool arg1Changed, uint256 arg1Bal) = _extractMappingChange(edslResult, 2, arg1);
        if (arg1Changed) edslBalances[arg1] = arg1Bal;

        (bool aChanged, uint256 allowanceA) = _extractMapping2Change(edslResult, 3, sender, arg0);
        if (aChanged) edslAllowances[sender][arg0] = allowanceA;
        (bool bChanged, uint256 allowanceB) = _extractMapping2Change(edslResult, 3, arg0, sender);
        if (bChanged) edslAllowances[arg0][sender] = allowanceB;
        (bool cChanged, uint256 allowanceC) = _extractMapping2Change(edslResult, 3, arg0, arg1);
        if (cChanged) edslAllowances[arg0][arg1] = allowanceC;
    }

    function executeDifferentialTest(
        string memory functionName,
        address sender,
        address arg0,
        address arg1,
        uint256 arg2
    ) internal returns (bool) {
        vm.prank(sender);

        bool evmSuccess;
        bytes memory evmReturnData;

        bytes32 functionSig = keccak256(bytes(functionName));
        if (functionSig == keccak256(bytes("mint"))) {
            (evmSuccess, evmReturnData) = address(token).call(abi.encodeWithSignature("mint(address,uint256)", arg0, arg2));
        } else if (functionSig == keccak256(bytes("transfer"))) {
            (evmSuccess, evmReturnData) = address(token).call(abi.encodeWithSignature("transfer(address,uint256)", arg0, arg2));
        } else if (functionSig == keccak256(bytes("approve"))) {
            (evmSuccess, evmReturnData) = address(token).call(abi.encodeWithSignature("approve(address,uint256)", arg0, arg2));
        } else if (functionSig == keccak256(bytes("transferFrom"))) {
            (evmSuccess, evmReturnData) = address(token).call(
                abi.encodeWithSignature("transferFrom(address,address,uint256)", arg0, arg1, arg2)
            );
        } else if (functionSig == keccak256(bytes("balanceOf"))) {
            (evmSuccess, evmReturnData) = address(token).call(abi.encodeWithSignature("balanceOf(address)", arg0));
        } else if (functionSig == keccak256(bytes("allowanceOf"))) {
            (evmSuccess, evmReturnData) = address(token).call(abi.encodeWithSignature("allowanceOf(address,address)", arg0, arg1));
        } else if (functionSig == keccak256(bytes("totalSupply"))) {
            (evmSuccess, evmReturnData) = address(token).call(abi.encodeWithSignature("totalSupply()"));
        } else if (functionSig == keccak256(bytes("owner"))) {
            (evmSuccess, evmReturnData) = address(token).call(abi.encodeWithSignature("owner()"));
        } else {
            revert("Unknown function");
        }

        uint256 evmReturnValue = 0;
        address evmReturnAddress = address(0);
        if (evmSuccess && evmReturnData.length > 0) {
            if (functionSig == keccak256(bytes("owner"))) {
                evmReturnAddress = abi.decode(evmReturnData, (address));
            } else {
                evmReturnValue = abi.decode(evmReturnData, (uint256));
            }
        }

        string memory edslResult = _runInterpreter(
            functionName,
            sender,
            arg0,
            arg1,
            arg2,
            _buildMapState(sender, arg0, arg1),
            _buildMap2State(arg0, sender, arg1)
        );
        bool edslSuccess = contains(edslResult, "\"success\":true");

        if (evmSuccess != edslSuccess) {
            console2.log("MISMATCH success");
            testsFailed++;
            return false;
        }

        if (!contains(edslResult, "\"returnValue\":")) {
            console2.log("MISMATCH malformed JSON");
            testsFailed++;
            return false;
        }

        uint256 edslReturnValue = _extractReturnValue(edslResult);
        if (functionSig == keccak256(bytes("owner"))) {
            if (uint256(uint160(evmReturnAddress)) != edslReturnValue) {
                console2.log("MISMATCH owner return");
                testsFailed++;
                return false;
            }
        } else if (
            functionSig == keccak256(bytes("balanceOf"))
                || functionSig == keccak256(bytes("allowanceOf"))
                || functionSig == keccak256(bytes("totalSupply"))
        ) {
            if (evmReturnValue != edslReturnValue) {
                console2.log("MISMATCH uint return");
                testsFailed++;
                return false;
            }
        }

        _updateStateFromEDSL(edslResult, sender, arg0, arg1);

        if (token.totalSupply() != edslStorage[1]) {
            console2.log("MISMATCH totalSupply state");
            testsFailed++;
            return false;
        }
        if (token.owner() != edslStorageAddr[0]) {
            console2.log("MISMATCH owner state");
            testsFailed++;
            return false;
        }
        if (token.balanceOf(sender) != edslBalances[sender]) {
            console2.log("MISMATCH sender balance");
            testsFailed++;
            return false;
        }
        if (token.balanceOf(arg0) != edslBalances[arg0]) {
            console2.log("MISMATCH arg0 balance");
            testsFailed++;
            return false;
        }
        if (token.balanceOf(arg1) != edslBalances[arg1]) {
            console2.log("MISMATCH arg1 balance");
            testsFailed++;
            return false;
        }
        if (token.allowanceOf(arg0, sender) != edslAllowances[arg0][sender]) {
            console2.log("MISMATCH allowance (arg0,sender)");
            testsFailed++;
            return false;
        }
        if (token.allowanceOf(arg0, arg1) != edslAllowances[arg0][arg1]) {
            console2.log("MISMATCH allowance (arg0,arg1)");
            testsFailed++;
            return false;
        }

        testsPassed++;
        return true;
    }

    function testDifferential_MintApproveTransferFromAndViews() public {
        address alice = address(0xA11CE);
        address bob = address(0xB0B);

        assertTrue(executeDifferentialTest("mint", address(this), alice, address(0), 100));
        assertTrue(executeDifferentialTest("approve", alice, bob, address(0), 60));
        assertTrue(executeDifferentialTest("allowanceOf", address(this), alice, bob, 0));
        assertTrue(executeDifferentialTest("transferFrom", bob, alice, bob, 40));
        assertTrue(executeDifferentialTest("allowanceOf", address(this), alice, bob, 0));
        assertTrue(executeDifferentialTest("balanceOf", address(this), alice, address(0), 0));
        assertTrue(executeDifferentialTest("balanceOf", address(this), bob, address(0), 0));
        assertTrue(executeDifferentialTest("totalSupply", address(this), address(0), address(0), 0));
    }

    function testDifferential_MaxAllowanceTransferFromParity() public {
        address alice = address(0xAA11CE);
        address spender = address(0xBEEF);
        address bob = address(0xB0B);

        assertTrue(executeDifferentialTest("mint", address(this), alice, address(0), 90));
        assertTrue(executeDifferentialTest("approve", alice, spender, address(0), type(uint256).max));
        assertTrue(executeDifferentialTest("transferFrom", spender, alice, bob, 25));
        assertTrue(executeDifferentialTest("allowanceOf", address(this), alice, spender, 0));
    }

    function testDifferential_RevertParity() public {
        address alice = address(0xA11CE);
        address bob = address(0xB0B);

        assertTrue(executeDifferentialTest("mint", address(0xDEAD), alice, address(0), 7));
        assertTrue(executeDifferentialTest("transferFrom", bob, alice, bob, 1));
    }

    function testDifferential_TransferInsufficientBalance() public {
        address alice = address(0xA11CE);
        address bob = address(0xB0B);

        // Mint 50 to Alice
        assertTrue(executeDifferentialTest("mint", address(this), alice, address(0), 50));
        // Alice tries to transfer 100 (more than her 50 balance) — should revert
        assertTrue(executeDifferentialTest("transfer", alice, bob, address(0), 100));
    }

    function testDifferential_TransferFromInsufficientBalance() public {
        address alice = address(0xA11CE);
        address bob = address(0xB0B);
        address spender = address(0xBEEF);

        // Mint 30 to Alice, approve spender for 100
        assertTrue(executeDifferentialTest("mint", address(this), alice, address(0), 30));
        assertTrue(executeDifferentialTest("approve", alice, spender, address(0), 100));
        // Spender tries to transferFrom 50 (Alice only has 30) — should revert
        assertTrue(executeDifferentialTest("transferFrom", spender, alice, bob, 50));
    }

    function testDifferential_TransferFromInsufficientAllowance() public {
        address alice = address(0xA11CE);
        address bob = address(0xB0B);
        address spender = address(0xBEEF);

        // Mint 100 to Alice, approve spender for only 20
        assertTrue(executeDifferentialTest("mint", address(this), alice, address(0), 100));
        assertTrue(executeDifferentialTest("approve", alice, spender, address(0), 20));
        // Spender tries to transferFrom 50 (allowance is only 20) — should revert
        assertTrue(executeDifferentialTest("transferFrom", spender, alice, bob, 50));
    }

    function testDifferential_TransferZeroAmount() public {
        address alice = address(0xA11CE);
        address bob = address(0xB0B);

        // Transfer 0 with no balance — should succeed (0 >= 0)
        assertTrue(executeDifferentialTest("transfer", alice, bob, address(0), 0));
    }

    function testDifferential_TransferFromZeroAmount() public {
        address alice = address(0xA11CE);
        address bob = address(0xB0B);
        address spender = address(0xBEEF);

        // Approve 0, transferFrom 0 — should succeed (0 >= 0 for both checks)
        assertTrue(executeDifferentialTest("approve", alice, spender, address(0), 0));
        assertTrue(executeDifferentialTest("transferFrom", spender, alice, bob, 0));
    }

    function testDifferential_TransferFromExactAllowance() public {
        address alice = address(0xA11CE);
        address bob = address(0xB0B);
        address spender = address(0xBEEF);

        // Mint 100 to Alice, approve spender for exactly 40
        assertTrue(executeDifferentialTest("mint", address(this), alice, address(0), 100));
        assertTrue(executeDifferentialTest("approve", alice, spender, address(0), 40));
        // TransferFrom exactly 40 — should succeed and consume allowance
        assertTrue(executeDifferentialTest("transferFrom", spender, alice, bob, 40));
        // TransferFrom 1 more — should revert (allowance is now 0)
        assertTrue(executeDifferentialTest("transferFrom", spender, alice, bob, 1));
    }
}
