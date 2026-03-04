// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import {Test, console2} from "forge-std/Test.sol";
import "./DiffTestConfig.sol";
import "./DifferentialTestBase.sol";

contract ERC721DiffModel {
    address private _owner;
    uint256 private _totalSupply;
    uint256 private _nextTokenId;
    mapping(address => uint256) private _balances;
    mapping(uint256 => address) private _owners;
    mapping(uint256 => address) private _tokenApprovals;
    mapping(address => mapping(address => bool)) private _operatorApprovals;

    constructor(address initialOwner) {
        _owner = initialOwner;
        _totalSupply = 0;
        _nextTokenId = 0;
    }

    function owner() external view returns (address) { return _owner; }
    function totalSupply() external view returns (uint256) { return _totalSupply; }
    function nextTokenId() external view returns (uint256) { return _nextTokenId; }
    function balanceOf(address addr) external view returns (uint256) { return _balances[addr]; }

    function ownerOf(uint256 tokenId) public view returns (address) {
        address tokenOwner = _owners[tokenId];
        require(tokenOwner != address(0), "Token does not exist");
        return tokenOwner;
    }

    function getApproved(uint256 tokenId) external view returns (address) {
        ownerOf(tokenId);
        return _tokenApprovals[tokenId];
    }

    function isApprovedForAll(address ownerAddr, address operator) external view returns (bool) {
        return _operatorApprovals[ownerAddr][operator];
    }

    function mint(address to) external returns (uint256) {
        require(msg.sender == _owner, "Caller is not the owner");
        require(to != address(0), "Invalid recipient");

        uint256 tokenId = _nextTokenId;
        require(_owners[tokenId] == address(0), "Token already minted");

        _owners[tokenId] = to;
        _balances[to] += 1;
        _totalSupply += 1;
        _nextTokenId = tokenId + 1;
        return tokenId;
    }

    function approve(address approved, uint256 tokenId) external {
        address tokenOwner = ownerOf(tokenId);
        require(msg.sender == tokenOwner, "Not token owner");
        _tokenApprovals[tokenId] = approved;
    }

    function setApprovalForAll(address operator, bool approved) external {
        _operatorApprovals[msg.sender][operator] = approved;
    }

    function transferFrom(address fromAddr, address to, uint256 tokenId) external {
        require(to != address(0), "Invalid recipient");
        address tokenOwner = ownerOf(tokenId);
        require(tokenOwner == fromAddr, "From is not owner");

        bool authorized = msg.sender == fromAddr
            || _tokenApprovals[tokenId] == msg.sender
            || _operatorApprovals[fromAddr][msg.sender];
        require(authorized, "Not authorized");

        if (fromAddr != to) {
            require(_balances[fromAddr] >= 1, "Insufficient balance");
            _balances[fromAddr] -= 1;
            _balances[to] += 1;
        }

        _owners[tokenId] = to;
        _tokenApprovals[tokenId] = address(0);
    }
}

import "./yul/YulTestBase.sol";

contract DifferentialERC721 is YulTestBase, DiffTestConfig, DifferentialTestBase {
    ERC721DiffModel private nft;

    mapping(address => uint256) private edslBalances; // slot 3
    mapping(uint256 => uint256) private edslStorage; // slot 1 => totalSupply, slot 2 => nextTokenId
    mapping(uint256 => address) private edslStorageAddr; // slot 0 => owner
    mapping(uint256 => address) private edslOwners; // slot 4
    mapping(uint256 => address) private edslTokenApprovals; // slot 5
    mapping(address => mapping(address => bool)) private edslOperatorApprovals; // slot 6

    function setUp() public {
        nft = new ERC721DiffModel(address(this));
        edslStorage[1] = 0;
        edslStorage[2] = 0;
        edslStorageAddr[0] = address(this);
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
            out = string.concat(out, "3:", _toLowerCase(vm.toString(k)), ":", vm.toString(edslBalances[k]));
            first = false;
        }

        return out;
    }

    function _buildMapUintState(uint256 tokenId) internal view returns (string memory) {
        return string.concat(
            "4:",
            vm.toString(tokenId),
            ":",
            vm.toString(uint256(uint160(edslOwners[tokenId]))),
            ",5:",
            vm.toString(tokenId),
            ":",
            vm.toString(uint256(uint160(edslTokenApprovals[tokenId])))
        );
    }

    function _buildMap2State(address ownerAddr, address operatorA, address operatorB) internal view returns (string memory) {
        string memory out = "";
        bool first = true;

        uint256 flagA = edslOperatorApprovals[ownerAddr][operatorA] ? 1 : 0;
        if (flagA > 0) {
            out = string.concat(
                "6:",
                _toLowerCase(vm.toString(ownerAddr)),
                ":",
                _toLowerCase(vm.toString(operatorA)),
                ":",
                vm.toString(flagA)
            );
            first = false;
        }

        if (operatorB != operatorA) {
            uint256 flagB = edslOperatorApprovals[ownerAddr][operatorB] ? 1 : 0;
            if (flagB > 0) {
                if (!first) out = string.concat(out, ",");
                out = string.concat(
                    out,
                    "6:",
                    _toLowerCase(vm.toString(ownerAddr)),
                    ":",
                    _toLowerCase(vm.toString(operatorB)),
                    ":",
                    vm.toString(flagB)
                );
            }
        }

        return out;
    }

    function _runInterpreter(
        string memory functionName,
        address sender,
        address arg0,
        address arg1,
        uint256 arg2,
        uint256 tokenIdHint
    ) internal returns (string memory) {
        string[] memory inputs = new string[](3);
        inputs[0] = "bash";
        inputs[1] = "-c";

        bytes32 functionSig = keccak256(bytes(functionName));
        string memory argsStr = "";

        if (functionSig == keccak256(bytes("mint")) || functionSig == keccak256(bytes("balanceOf"))) {
            argsStr = vm.toString(uint256(uint160(arg0)));
        } else if (functionSig == keccak256(bytes("ownerOf")) || functionSig == keccak256(bytes("getApproved"))) {
            argsStr = vm.toString(arg2);
        } else if (functionSig == keccak256(bytes("approve")) || functionSig == keccak256(bytes("setApprovalForAll"))) {
            argsStr = string.concat(vm.toString(uint256(uint160(arg0))), " ", vm.toString(arg2));
        } else if (functionSig == keccak256(bytes("isApprovedForAll"))) {
            argsStr = string.concat(vm.toString(uint256(uint160(arg0))), " ", vm.toString(uint256(uint160(arg1))));
        } else if (functionSig == keccak256(bytes("transferFrom"))) {
            argsStr = string.concat(
                vm.toString(uint256(uint160(arg0))),
                " ",
                vm.toString(uint256(uint160(arg1))),
                " ",
                vm.toString(arg2)
            );
        }

        string memory storageStr = string.concat("storage=1:", vm.toString(edslStorage[1]), ",2:", vm.toString(edslStorage[2]));
        string memory addrStr = string.concat("addr=0:", _addressToString(edslStorageAddr[0]));
        string memory mapStr = _buildMapState(sender, arg0, arg1);

        string memory map2Str;
        if (functionSig == keccak256(bytes("setApprovalForAll"))) {
            map2Str = _buildMap2State(sender, arg0, arg1);
        } else if (functionSig == keccak256(bytes("isApprovedForAll"))) {
            map2Str = _buildMap2State(arg0, arg1, sender);
        } else if (functionSig == keccak256(bytes("transferFrom"))) {
            map2Str = _buildMap2State(arg0, sender, arg1);
        } else {
            map2Str = _buildMap2State(arg0, sender, arg1);
        }

        string memory mapUintStr = _buildMapUintState(tokenIdHint);

        inputs[2] = string.concat(
            _interpreterPreamble(),
            " ERC721 ",
            functionName,
            " ",
            _addressToString(sender),
            bytes(argsStr).length > 0 ? string.concat(" ", argsStr) : "",
            " ",
            storageStr,
            " ",
            addrStr,
            bytes(mapStr).length > 0 ? string.concat(" map=\"", mapStr, "\"") : "",
            " mapuint=\"",
            mapUintStr,
            "\"",
            bytes(map2Str).length > 0 ? string.concat(" map2=\"", map2Str, "\"") : "",
            " value=0 timestamp=",
            vm.toString(block.timestamp)
        );

        return string(vm.ffi(inputs));
    }

    function _ownerOfModel(uint256 tokenId) internal view returns (bool, address) {
        (bool ok, bytes memory data) = address(nft).staticcall(abi.encodeWithSignature("ownerOf(uint256)", tokenId));
        if (!ok || data.length == 0) return (false, address(0));
        return (true, abi.decode(data, (address)));
    }

    function _getApprovedModel(uint256 tokenId) internal view returns (bool, address) {
        (bool ok, bytes memory data) = address(nft).staticcall(abi.encodeWithSignature("getApproved(uint256)", tokenId));
        if (!ok || data.length == 0) return (false, address(0));
        return (true, abi.decode(data, (address)));
    }

    function _updateStateFromEDSL(
        string memory edslResult,
        address sender,
        address arg0,
        address arg1,
        uint256 tokenIdHint
    ) internal {
        (bool hasSupply, uint256 supplyVal) = _extractStorageChange(edslResult, 1);
        if (hasSupply) edslStorage[1] = supplyVal;

        (bool hasNextToken, uint256 nextTokenVal) = _extractStorageChange(edslResult, 2);
        if (hasNextToken) edslStorage[2] = nextTokenVal;

        (bool hasOwnerSlot, uint256 ownerNat) = _extractStorageAddrChange(edslResult, 0);
        if (hasOwnerSlot) edslStorageAddr[0] = address(uint160(ownerNat));

        (bool senderChanged, uint256 senderBal) = _extractMappingChange(edslResult, 3, sender);
        if (senderChanged) edslBalances[sender] = senderBal;
        (bool arg0Changed, uint256 arg0Bal) = _extractMappingChange(edslResult, 3, arg0);
        if (arg0Changed) edslBalances[arg0] = arg0Bal;
        (bool arg1Changed, uint256 arg1Bal) = _extractMappingChange(edslResult, 3, arg1);
        if (arg1Changed) edslBalances[arg1] = arg1Bal;

        (bool ownerWordChanged, uint256 ownerWord) = _extractMappingUintChange(edslResult, 4, tokenIdHint);
        if (ownerWordChanged) edslOwners[tokenIdHint] = address(uint160(ownerWord));

        (bool approvalWordChanged, uint256 approvalWord) = _extractMappingUintChange(edslResult, 5, tokenIdHint);
        if (approvalWordChanged) edslTokenApprovals[tokenIdHint] = address(uint160(approvalWord));

        (bool opAChanged, uint256 opAWord) = _extractMapping2Change(edslResult, 6, arg0, sender);
        if (opAChanged) edslOperatorApprovals[arg0][sender] = opAWord != 0;

        (bool opBChanged, uint256 opBWord) = _extractMapping2Change(edslResult, 6, sender, arg0);
        if (opBChanged) edslOperatorApprovals[sender][arg0] = opBWord != 0;

        (bool opCChanged, uint256 opCWord) = _extractMapping2Change(edslResult, 6, arg0, arg1);
        if (opCChanged) edslOperatorApprovals[arg0][arg1] = opCWord != 0;
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
            (evmSuccess, evmReturnData) = address(nft).call(abi.encodeWithSignature("mint(address)", arg0));
        } else if (functionSig == keccak256(bytes("balanceOf"))) {
            (evmSuccess, evmReturnData) = address(nft).call(abi.encodeWithSignature("balanceOf(address)", arg0));
        } else if (functionSig == keccak256(bytes("ownerOf"))) {
            (evmSuccess, evmReturnData) = address(nft).call(abi.encodeWithSignature("ownerOf(uint256)", arg2));
        } else if (functionSig == keccak256(bytes("approve"))) {
            (evmSuccess, evmReturnData) = address(nft).call(abi.encodeWithSignature("approve(address,uint256)", arg0, arg2));
        } else if (functionSig == keccak256(bytes("getApproved"))) {
            (evmSuccess, evmReturnData) = address(nft).call(abi.encodeWithSignature("getApproved(uint256)", arg2));
        } else if (functionSig == keccak256(bytes("setApprovalForAll"))) {
            (evmSuccess, evmReturnData) = address(nft).call(abi.encodeWithSignature("setApprovalForAll(address,bool)", arg0, arg2 != 0));
        } else if (functionSig == keccak256(bytes("isApprovedForAll"))) {
            (evmSuccess, evmReturnData) = address(nft).call(abi.encodeWithSignature("isApprovedForAll(address,address)", arg0, arg1));
        } else if (functionSig == keccak256(bytes("transferFrom"))) {
            (evmSuccess, evmReturnData) = address(nft).call(
                abi.encodeWithSignature("transferFrom(address,address,uint256)", arg0, arg1, arg2)
            );
        } else if (functionSig == keccak256(bytes("totalSupply"))) {
            (evmSuccess, evmReturnData) = address(nft).call(abi.encodeWithSignature("totalSupply()"));
        } else if (functionSig == keccak256(bytes("nextTokenId"))) {
            (evmSuccess, evmReturnData) = address(nft).call(abi.encodeWithSignature("nextTokenId()"));
        } else if (functionSig == keccak256(bytes("owner"))) {
            (evmSuccess, evmReturnData) = address(nft).call(abi.encodeWithSignature("owner()"));
        } else {
            revert("Unknown function");
        }

        uint256 evmReturnValue = 0;
        if (evmSuccess && evmReturnData.length > 0) {
            evmReturnValue = abi.decode(evmReturnData, (uint256));
        }

        uint256 tokenIdHint = arg2;
        if (functionSig == keccak256(bytes("mint")) && evmSuccess) tokenIdHint = evmReturnValue;

        string memory edslResult = _runInterpreter(functionName, sender, arg0, arg1, arg2, tokenIdHint);
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
        if (
            functionSig == keccak256(bytes("balanceOf"))
                || functionSig == keccak256(bytes("totalSupply"))
                || functionSig == keccak256(bytes("nextTokenId"))
                || functionSig == keccak256(bytes("mint"))
                || functionSig == keccak256(bytes("isApprovedForAll"))
                || functionSig == keccak256(bytes("owner"))
                || functionSig == keccak256(bytes("ownerOf"))
                || functionSig == keccak256(bytes("getApproved"))
        ) {
            if (evmSuccess && evmReturnValue != edslReturnValue) {
                console2.log("MISMATCH return value");
                testsFailed++;
                return false;
            }
        }

        _updateStateFromEDSL(edslResult, sender, arg0, arg1, tokenIdHint);

        if (nft.totalSupply() != edslStorage[1]) {
            console2.log("MISMATCH totalSupply");
            testsFailed++;
            return false;
        }
        if (nft.nextTokenId() != edslStorage[2]) {
            console2.log("MISMATCH nextTokenId");
            testsFailed++;
            return false;
        }
        if (nft.owner() != edslStorageAddr[0]) {
            console2.log("MISMATCH owner slot");
            testsFailed++;
            return false;
        }
        if (nft.balanceOf(sender) != edslBalances[sender]) {
            console2.log("MISMATCH sender balance");
            testsFailed++;
            return false;
        }
        if (nft.balanceOf(arg0) != edslBalances[arg0]) {
            console2.log("MISMATCH arg0 balance");
            testsFailed++;
            return false;
        }
        if (nft.balanceOf(arg1) != edslBalances[arg1]) {
            console2.log("MISMATCH arg1 balance");
            testsFailed++;
            return false;
        }

        (bool ownerOk, address ownerVal) = _ownerOfModel(tokenIdHint);
        if (ownerOk && ownerVal != edslOwners[tokenIdHint]) {
            console2.log("MISMATCH ownerOf map");
            testsFailed++;
            return false;
        }

        (bool apprOk, address apprVal) = _getApprovedModel(tokenIdHint);
        if (apprOk && apprVal != edslTokenApprovals[tokenIdHint]) {
            console2.log("MISMATCH getApproved map");
            testsFailed++;
            return false;
        }

        if (nft.isApprovedForAll(arg0, sender) != edslOperatorApprovals[arg0][sender]) {
            console2.log("MISMATCH operator approvals");
            testsFailed++;
            return false;
        }
        if (nft.isApprovedForAll(arg0, arg1) != edslOperatorApprovals[arg0][arg1]) {
            console2.log("MISMATCH operator approvals arg1");
            testsFailed++;
            return false;
        }

        testsPassed++;
        return true;
    }

    function testDifferential_OwnerApproveAndTransferFromParity() public {
        address alice = address(0xA11CE);
        address bob = address(0xB0B);

        assertTrue(executeDifferentialTest("mint", address(this), alice, address(0), 0));
        assertTrue(executeDifferentialTest("ownerOf", address(this), address(0), address(0), 0));
        assertTrue(executeDifferentialTest("approve", alice, bob, address(0), 0));
        assertTrue(executeDifferentialTest("getApproved", address(this), address(0), address(0), 0));
        assertTrue(executeDifferentialTest("transferFrom", bob, alice, bob, 0));
        assertTrue(executeDifferentialTest("ownerOf", address(this), address(0), address(0), 0));
    }

    function testDifferential_OperatorApprovalParity() public {
        address alice = address(0xA11CE);
        address operator = address(0x0F3);
        address bob = address(0xB0B);

        assertTrue(executeDifferentialTest("mint", address(this), alice, address(0), 0));
        assertTrue(executeDifferentialTest("setApprovalForAll", alice, operator, address(0), 1));
        assertTrue(executeDifferentialTest("isApprovedForAll", address(this), alice, operator, 0));
        assertTrue(executeDifferentialTest("transferFrom", operator, alice, bob, 0));
        assertTrue(executeDifferentialTest("ownerOf", address(this), address(0), address(0), 0));
    }

    function testDifferential_RevertParity() public {
        address alice = address(0xA11CE);
        address bob = address(0xB0B);

        assertTrue(executeDifferentialTest("mint", address(0xDEAD), alice, address(0), 0));
        assertTrue(executeDifferentialTest("transferFrom", bob, alice, bob, 0));
    }

    function testDifferential_MintToZeroAddress() public {
        // Minting to address(0) should revert ("Invalid recipient")
        assertTrue(executeDifferentialTest("mint", address(this), address(0), address(0), 0));
    }

    function testDifferential_OwnerOfNonexistent() public {
        // ownerOf for a token that hasn't been minted should revert
        assertTrue(executeDifferentialTest("ownerOf", address(this), address(0), address(0), 99));
    }

    function testDifferential_ApproveNonexistentToken() public {
        address alice = address(0xA11CE);

        // Approve on a token that doesn't exist — ownerOf reverts internally
        assertTrue(executeDifferentialTest("approve", alice, address(0xB0B), address(0), 99));
    }

    function testDifferential_ApproveByNonOwner() public {
        address alice = address(0xA11CE);
        address bob = address(0xB0B);

        // Mint token 0 to Alice
        assertTrue(executeDifferentialTest("mint", address(this), alice, address(0), 0));
        // Bob tries to approve on Alice's token — should revert ("Not token owner")
        assertTrue(executeDifferentialTest("approve", bob, address(0xBEEF), address(0), 0));
    }

    function testDifferential_TransferFromNotAuthorized() public {
        address alice = address(0xA11CE);
        address bob = address(0xB0B);
        address carol = address(0xCA501);

        // Mint token 0 to Alice
        assertTrue(executeDifferentialTest("mint", address(this), alice, address(0), 0));
        // Carol (not owner, not approved, not operator) tries to transfer — should revert
        assertTrue(executeDifferentialTest("transferFrom", carol, alice, bob, 0));
    }

    function testDifferential_TransferFromToZeroAddress() public {
        address alice = address(0xA11CE);

        // Mint token 0 to Alice
        assertTrue(executeDifferentialTest("mint", address(this), alice, address(0), 0));
        // Alice tries to transfer to address(0) — should revert ("Invalid recipient")
        assertTrue(executeDifferentialTest("transferFrom", alice, alice, address(0), 0));
    }

    function testDifferential_TransferFromWrongOwner() public {
        address alice = address(0xA11CE);
        address bob = address(0xB0B);
        address carol = address(0xCA501);

        // Mint token 0 to Alice
        assertTrue(executeDifferentialTest("mint", address(this), alice, address(0), 0));
        // Alice tries transferFrom(bob, carol, 0) but bob is not the owner — should revert
        assertTrue(executeDifferentialTest("transferFrom", alice, bob, carol, 0));
    }

    function testDifferential_GetApprovedNonexistent() public {
        // getApproved for nonexistent token — ownerOf check reverts internally
        assertTrue(executeDifferentialTest("getApproved", address(this), address(0), address(0), 99));
    }

    // ---- Randomized multi-seed differential tests ----

    address[] private _actors;

    function _initActors() internal {
        _actors = new address[](5);
        _actors[0] = address(this); // Owner / deployer
        _actors[1] = address(0xA11CE);
        _actors[2] = address(0xB0B);
        _actors[3] = address(0xCA501);
        _actors[4] = address(0xDABE);
    }

    function _buildMapStateAll() internal view returns (string memory) {
        string memory out = "";
        bool first = true;
        for (uint256 i = 0; i < _actors.length; i++) {
            address k = _actors[i];
            if (edslBalances[k] == 0) continue;
            if (!first) out = string.concat(out, ",");
            out = string.concat(out, "3:", _toLowerCase(vm.toString(k)), ":", vm.toString(edslBalances[k]));
            first = false;
        }
        return out;
    }

    function _buildMapUintStateAll() internal view returns (string memory) {
        string memory out = "";
        bool first = true;
        uint256 nextId = edslStorage[2];
        for (uint256 t = 0; t < nextId; t++) {
            if (!first) out = string.concat(out, ",");
            out = string.concat(
                out,
                "4:",
                vm.toString(t),
                ":",
                vm.toString(uint256(uint160(edslOwners[t]))),
                ",5:",
                vm.toString(t),
                ":",
                vm.toString(uint256(uint160(edslTokenApprovals[t])))
            );
            first = false;
        }
        return out;
    }

    function _buildMap2StateAll() internal view returns (string memory) {
        string memory out = "";
        bool first = true;
        for (uint256 i = 0; i < _actors.length; i++) {
            for (uint256 j = 0; j < _actors.length; j++) {
                if (!edslOperatorApprovals[_actors[i]][_actors[j]]) continue;
                if (!first) out = string.concat(out, ",");
                out = string.concat(
                    out,
                    "6:",
                    _toLowerCase(vm.toString(_actors[i])),
                    ":",
                    _toLowerCase(vm.toString(_actors[j])),
                    ":1"
                );
                first = false;
            }
        }
        return out;
    }

    function _executeRandomDifferentialTest(
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
            (evmSuccess, evmReturnData) = address(nft).call(abi.encodeWithSignature("mint(address)", arg0));
        } else if (functionSig == keccak256(bytes("balanceOf"))) {
            (evmSuccess, evmReturnData) = address(nft).call(abi.encodeWithSignature("balanceOf(address)", arg0));
        } else if (functionSig == keccak256(bytes("ownerOf"))) {
            (evmSuccess, evmReturnData) = address(nft).call(abi.encodeWithSignature("ownerOf(uint256)", arg2));
        } else if (functionSig == keccak256(bytes("approve"))) {
            (evmSuccess, evmReturnData) = address(nft).call(abi.encodeWithSignature("approve(address,uint256)", arg0, arg2));
        } else if (functionSig == keccak256(bytes("getApproved"))) {
            (evmSuccess, evmReturnData) = address(nft).call(abi.encodeWithSignature("getApproved(uint256)", arg2));
        } else if (functionSig == keccak256(bytes("setApprovalForAll"))) {
            (evmSuccess, evmReturnData) = address(nft).call(abi.encodeWithSignature("setApprovalForAll(address,bool)", arg0, arg2 != 0));
        } else if (functionSig == keccak256(bytes("isApprovedForAll"))) {
            (evmSuccess, evmReturnData) = address(nft).call(abi.encodeWithSignature("isApprovedForAll(address,address)", arg0, arg1));
        } else if (functionSig == keccak256(bytes("transferFrom"))) {
            (evmSuccess, evmReturnData) = address(nft).call(
                abi.encodeWithSignature("transferFrom(address,address,uint256)", arg0, arg1, arg2)
            );
        } else if (functionSig == keccak256(bytes("totalSupply"))) {
            (evmSuccess, evmReturnData) = address(nft).call(abi.encodeWithSignature("totalSupply()"));
        } else if (functionSig == keccak256(bytes("nextTokenId"))) {
            (evmSuccess, evmReturnData) = address(nft).call(abi.encodeWithSignature("nextTokenId()"));
        } else if (functionSig == keccak256(bytes("owner"))) {
            (evmSuccess, evmReturnData) = address(nft).call(abi.encodeWithSignature("owner()"));
        } else {
            revert("Unknown function");
        }

        uint256 evmReturnValue = 0;
        if (evmSuccess && evmReturnData.length > 0) {
            evmReturnValue = abi.decode(evmReturnData, (uint256));
        }

        uint256 tokenIdHint = arg2;
        if (functionSig == keccak256(bytes("mint")) && evmSuccess) tokenIdHint = evmReturnValue;

        // Build full state strings for the interpreter
        string memory mapStr = _buildMapStateAll();
        string memory mapUintStr = _buildMapUintStateAll();
        string memory map2Str = _buildMap2StateAll();

        string[] memory inputs = new string[](3);
        inputs[0] = "bash";
        inputs[1] = "-c";

        string memory argsStr = "";
        if (functionSig == keccak256(bytes("mint")) || functionSig == keccak256(bytes("balanceOf"))) {
            argsStr = vm.toString(uint256(uint160(arg0)));
        } else if (functionSig == keccak256(bytes("ownerOf")) || functionSig == keccak256(bytes("getApproved"))) {
            argsStr = vm.toString(arg2);
        } else if (functionSig == keccak256(bytes("approve")) || functionSig == keccak256(bytes("setApprovalForAll"))) {
            argsStr = string.concat(vm.toString(uint256(uint160(arg0))), " ", vm.toString(arg2));
        } else if (functionSig == keccak256(bytes("isApprovedForAll"))) {
            argsStr = string.concat(vm.toString(uint256(uint160(arg0))), " ", vm.toString(uint256(uint160(arg1))));
        } else if (functionSig == keccak256(bytes("transferFrom"))) {
            argsStr = string.concat(
                vm.toString(uint256(uint160(arg0))),
                " ",
                vm.toString(uint256(uint160(arg1))),
                " ",
                vm.toString(arg2)
            );
        }

        string memory storageStr = string.concat("storage=1:", vm.toString(edslStorage[1]), ",2:", vm.toString(edslStorage[2]));
        string memory addrStr = string.concat("addr=0:", _addressToString(edslStorageAddr[0]));

        inputs[2] = string.concat(
            _interpreterPreamble(),
            " ERC721 ",
            functionName,
            " ",
            _addressToString(sender),
            bytes(argsStr).length > 0 ? string.concat(" ", argsStr) : "",
            " ",
            storageStr,
            " ",
            addrStr,
            bytes(mapStr).length > 0 ? string.concat(" map=\"", mapStr, "\"") : "",
            " mapuint=\"",
            mapUintStr,
            "\"",
            bytes(map2Str).length > 0 ? string.concat(" map2=\"", map2Str, "\"") : "",
            " value=0 timestamp=",
            vm.toString(block.timestamp)
        );

        string memory edslResult = string(vm.ffi(inputs));
        bool edslSuccess = contains(edslResult, "\"success\":true");

        if (evmSuccess != edslSuccess) {
            testsFailed++;
            return false;
        }

        if (!contains(edslResult, "\"returnValue\":")) {
            testsFailed++;
            return false;
        }

        uint256 edslReturnValue = _extractReturnValue(edslResult);
        if (
            functionSig == keccak256(bytes("balanceOf"))
                || functionSig == keccak256(bytes("totalSupply"))
                || functionSig == keccak256(bytes("nextTokenId"))
                || functionSig == keccak256(bytes("mint"))
                || functionSig == keccak256(bytes("isApprovedForAll"))
                || functionSig == keccak256(bytes("owner"))
                || functionSig == keccak256(bytes("ownerOf"))
                || functionSig == keccak256(bytes("getApproved"))
        ) {
            if (evmSuccess && evmReturnValue != edslReturnValue) {
                testsFailed++;
                return false;
            }
        }

        _updateStateFromEDSL(edslResult, sender, arg0, arg1, tokenIdHint);

        if (nft.totalSupply() != edslStorage[1]) {
            testsFailed++;
            return false;
        }
        if (nft.nextTokenId() != edslStorage[2]) {
            testsFailed++;
            return false;
        }
        if (nft.owner() != edslStorageAddr[0]) {
            testsFailed++;
            return false;
        }
        for (uint256 i = 0; i < _actors.length; i++) {
            if (nft.balanceOf(_actors[i]) != edslBalances[_actors[i]]) {
                testsFailed++;
                return false;
            }
        }
        uint256 mintedCount = edslStorage[2]; // nextTokenId == number of minted tokens
        for (uint256 t = 0; t < mintedCount; t++) {
            (bool ownerOk, address ownerVal) = _ownerOfModel(t);
            if (ownerOk && ownerVal != edslOwners[t]) {
                testsFailed++;
                return false;
            }
            (bool apprOk, address apprVal) = _getApprovedModel(t);
            if (apprOk && apprVal != edslTokenApprovals[t]) {
                testsFailed++;
                return false;
            }
        }
        for (uint256 i = 0; i < _actors.length; i++) {
            for (uint256 j = 0; j < _actors.length; j++) {
                if (nft.isApprovedForAll(_actors[i], _actors[j]) != edslOperatorApprovals[_actors[i]][_actors[j]]) {
                    testsFailed++;
                    return false;
                }
            }
        }

        testsPassed++;
        return true;
    }

    function _randomTransaction(uint256 seed)
        internal
        view
        returns (
            string memory funcName,
            address sender,
            address arg0,
            address arg1,
            uint256 arg2
        )
    {
        uint256 rand1 = _lcg(seed);
        uint256 rand2 = _lcg(rand1);
        uint256 rand3 = _lcg(rand2);
        uint256 rand4 = _lcg(rand3);
        uint256 rand5 = _lcg(rand4);

        uint256 nextId = edslStorage[2];

        // Choose function (30% mint, 20% transferFrom, 15% approve, 10% setApprovalForAll, 25% views)
        uint256 funcChoice = rand1 % 100;
        if (funcChoice < 30) {
            funcName = "mint";
        } else if (funcChoice < 50) {
            funcName = "transferFrom";
        } else if (funcChoice < 65) {
            funcName = "approve";
        } else if (funcChoice < 75) {
            funcName = "setApprovalForAll";
        } else if (funcChoice < 80) {
            funcName = "balanceOf";
        } else if (funcChoice < 85) {
            funcName = "ownerOf";
        } else if (funcChoice < 90) {
            funcName = "getApproved";
        } else if (funcChoice < 95) {
            funcName = "isApprovedForAll";
        } else {
            funcName = "totalSupply";
        }

        // Sender: 50% owner (for mint), 50% random actor
        uint256 senderChoice = rand2 % 100;
        if (senderChoice < 50) {
            sender = edslStorageAddr[0];
        } else {
            sender = _actors[rand2 % _actors.length];
        }

        arg0 = _actors[rand3 % _actors.length];
        arg1 = _actors[rand4 % _actors.length];

        // For token-ID-based operations, use existing token IDs when possible
        if (nextId > 0) {
            arg2 = rand5 % (nextId + 1); // +1 to occasionally test nonexistent token
        } else {
            arg2 = 0;
        }

        // For setApprovalForAll, arg2 is a boolean (0 or 1)
        bytes32 sig = keccak256(bytes(funcName));
        if (sig == keccak256(bytes("setApprovalForAll"))) {
            arg2 = rand5 % 2;
        }
    }

    function testDifferential_Random100() public {
        _initActors();

        (uint256 startIndex, uint256 count) = _diffRandomSmallRange();
        uint256 seed = _diffRandomSeed("ERC721");

        for (uint256 i = 0; i < count; i++) {
            (
                string memory funcName,
                address sender,
                address arg0,
                address arg1,
                uint256 arg2
            ) = _randomTransaction(seed + startIndex + i);

            bool success = _executeRandomDifferentialTest(funcName, sender, arg0, arg1, arg2);
            _assertRandomSuccess(success, startIndex + i);
        }

        if (_diffVerbose()) console2.log("Random tests passed:", testsPassed);
        if (_diffVerbose()) console2.log("Random tests failed:", testsFailed);
        assertEq(testsFailed, 0, "Some random tests failed");
    }

    function testDifferential_Random10000() public {
        _initActors();

        (uint256 startIndex, uint256 count) = _diffRandomLargeRange();
        uint256 seed = _diffRandomSeed("ERC721");

        vm.pauseGasMetering();
        for (uint256 i = 0; i < count; i++) {
            (
                string memory funcName,
                address sender,
                address arg0,
                address arg1,
                uint256 arg2
            ) = _randomTransaction(seed + startIndex + i);

            bool success = _executeRandomDifferentialTest(funcName, sender, arg0, arg1, arg2);
            _assertRandomSuccess(success, startIndex + i);
        }
        vm.resumeGasMetering();

        if (_diffVerbose()) console2.log("Random tests passed:", testsPassed);
        if (_diffVerbose()) console2.log("Random tests failed:", testsFailed);
        assertEq(testsFailed, 0, "Some random tests failed");
    }
}
