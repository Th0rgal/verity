// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "forge-std/Test.sol";

struct MarketParamsParity {
    address loanToken;
    address collateralToken;
    address oracle;
    address irm;
    uint256 lltv;
}

struct DynamicTupleParity {
    uint256 amount;
    bytes payload;
}

struct StaticTupleParity {
    uint256 amount;
    address recipient;
}

contract EventAbiParityEmitter {
    event CreateMarket(bytes32 indexed id, MarketParamsParity market);
    event CompositeEvent(bytes32 indexed id, DynamicTupleParity payload, uint256[] values, bytes note);
    event IndexedBytes(bytes indexed payload);
    event IndexedStaticTuple(StaticTupleParity indexed payload);
    event IndexedStaticFixedArray(uint256[2] indexed payload);
    event IndexedDynamicStaticTupleArray(StaticTupleParity[] indexed payload);
    event IndexedDynamicStaticFixedArray(address[2][] indexed payload);
    event IndexedDynamicUintArray(uint256[] indexed payload);
    event IndexedDynamicAddressArray(address[] indexed payload);
    event IndexedDynamicBoolArray(bool[] indexed payload);
    event IndexedDynamicBytes32Array(bytes32[] indexed payload);
    event UnindexedDynamicStaticTupleArray(StaticTupleParity[] payload);
    event UnindexedDynamicUintArray(uint256[] payload);
    event UnindexedDynamicAddressArray(address[] payload);
    event UnindexedDynamicBoolArray(bool[] payload);
    event UnindexedDynamicBytes32Array(bytes32[] payload);
    event UnindexedDynamicStaticFixedArray(address[2][] payload);
    event UnindexedStaticTuple(StaticTupleParity payload);
    event UnindexedStaticFixedArray(uint256[2] payload);

    function emitCreateMarket(bytes32 id, MarketParamsParity calldata market) external {
        emit CreateMarket(id, market);
    }

    function emitCompositeEvent(
        bytes32 id,
        DynamicTupleParity calldata payload,
        uint256[] calldata values,
        bytes calldata note
    ) external {
        emit CompositeEvent(id, payload, values, note);
    }

    function emitIndexedBytes(bytes calldata payload) external {
        emit IndexedBytes(payload);
    }

    function emitIndexedStaticTuple(StaticTupleParity calldata payload) external {
        emit IndexedStaticTuple(payload);
    }

    function emitIndexedStaticFixedArray(uint256[2] calldata payload) external {
        emit IndexedStaticFixedArray(payload);
    }

    function emitIndexedDynamicStaticTupleArray(StaticTupleParity[] calldata payload) external {
        emit IndexedDynamicStaticTupleArray(payload);
    }

    function emitIndexedDynamicStaticFixedArray(address[2][] calldata payload) external {
        emit IndexedDynamicStaticFixedArray(payload);
    }

    function emitIndexedDynamicUintArray(uint256[] calldata payload) external {
        emit IndexedDynamicUintArray(payload);
    }

    function emitIndexedDynamicAddressArray(address[] calldata payload) external {
        emit IndexedDynamicAddressArray(payload);
    }

    function emitIndexedDynamicBoolArray(bool[] calldata payload) external {
        emit IndexedDynamicBoolArray(payload);
    }

    function emitIndexedDynamicBytes32Array(bytes32[] calldata payload) external {
        emit IndexedDynamicBytes32Array(payload);
    }

    function emitUnindexedDynamicStaticTupleArray(StaticTupleParity[] calldata payload) external {
        emit UnindexedDynamicStaticTupleArray(payload);
    }

    function emitUnindexedDynamicUintArray(uint256[] calldata payload) external {
        emit UnindexedDynamicUintArray(payload);
    }

    function emitUnindexedDynamicAddressArray(address[] calldata payload) external {
        emit UnindexedDynamicAddressArray(payload);
    }

    function emitUnindexedDynamicBoolArray(bool[] calldata payload) external {
        emit UnindexedDynamicBoolArray(payload);
    }

    function emitUnindexedDynamicBytes32Array(bytes32[] calldata payload) external {
        emit UnindexedDynamicBytes32Array(payload);
    }

    function emitUnindexedDynamicStaticFixedArray(address[2][] calldata payload) external {
        emit UnindexedDynamicStaticFixedArray(payload);
    }

    function emitUnindexedStaticTuple(StaticTupleParity calldata payload) external {
        emit UnindexedStaticTuple(payload);
    }

    function emitUnindexedStaticFixedArray(uint256[2] calldata payload) external {
        emit UnindexedStaticFixedArray(payload);
    }
}

contract EventAbiParityTest is Test {
    EventAbiParityEmitter internal emitter;

    function setUp() public {
        emitter = new EventAbiParityEmitter();
    }

    function testTopic0MatchesCreateMarketTupleSignature() public {
        bytes32 id = keccak256("market-id");
        MarketParamsParity memory market = MarketParamsParity({
            loanToken: address(0x1),
            collateralToken: address(0x2),
            oracle: address(0x3),
            irm: address(0x4),
            lltv: 940_000_000_000_000_000
        });

        vm.recordLogs();
        emitter.emitCreateMarket(id, market);

        Vm.Log[] memory logs = vm.getRecordedLogs();
        assertEq(logs.length, 1);
        assertEq(logs[0].topics.length, 2);

        bytes32 expectedTopic0 = keccak256(
            bytes("CreateMarket(bytes32,(address,address,address,address,uint256))")
        );

        assertEq(logs[0].topics[0], expectedTopic0);
        assertEq(logs[0].topics[1], id);
    }

    function testTopic0MatchesCompositeDynamicTupleSignature() public {
        bytes32 id = keccak256("composite-id");
        DynamicTupleParity memory payload = DynamicTupleParity({amount: 7, payload: hex"11223344"});
        uint256[] memory values = new uint256[](2);
        values[0] = 10;
        values[1] = 20;
        bytes memory note = hex"aabbcc";

        vm.recordLogs();
        emitter.emitCompositeEvent(id, payload, values, note);

        Vm.Log[] memory logs = vm.getRecordedLogs();
        assertEq(logs.length, 1);
        assertEq(logs[0].topics.length, 2);

        bytes32 expectedTopic0 = keccak256(
            bytes("CompositeEvent(bytes32,(uint256,bytes),uint256[],bytes)")
        );

        assertEq(logs[0].topics[0], expectedTopic0);
        assertEq(logs[0].topics[1], id);
    }

    function testIndexedBytesTopicHashesRawPayload() public {
        bytes memory payload = hex"deadbeefcafebabe";

        vm.recordLogs();
        emitter.emitIndexedBytes(payload);

        Vm.Log[] memory logs = vm.getRecordedLogs();
        assertEq(logs.length, 1);
        assertEq(logs[0].topics.length, 2);

        bytes32 expectedTopic0 = keccak256(bytes("IndexedBytes(bytes)"));
        bytes32 expectedTopic1 = keccak256(payload);

        assertEq(logs[0].topics[0], expectedTopic0);
        assertEq(logs[0].topics[1], expectedTopic1);
    }

    function testIndexedStaticTupleTopicUsesAbiEncodedTupleHash() public {
        StaticTupleParity memory payload = StaticTupleParity({
            amount: 123,
            recipient: address(0xBEEF)
        });

        vm.recordLogs();
        emitter.emitIndexedStaticTuple(payload);

        Vm.Log[] memory logs = vm.getRecordedLogs();
        assertEq(logs.length, 1);
        assertEq(logs[0].topics.length, 2);

        bytes32 expectedTopic0 = keccak256(bytes("IndexedStaticTuple((uint256,address))"));
        bytes32 expectedTopic1 = keccak256(abi.encode(payload.amount, payload.recipient));

        assertEq(logs[0].topics[0], expectedTopic0);
        assertEq(logs[0].topics[1], expectedTopic1);
    }

    function testIndexedStaticFixedArrayTopicUsesAbiEncodedArrayHash() public {
        uint256[2] memory payload = [uint256(777), uint256(888)];

        vm.recordLogs();
        emitter.emitIndexedStaticFixedArray(payload);

        Vm.Log[] memory logs = vm.getRecordedLogs();
        assertEq(logs.length, 1);
        assertEq(logs[0].topics.length, 2);

        bytes32 expectedTopic0 = keccak256(bytes("IndexedStaticFixedArray(uint256[2])"));
        bytes32 expectedTopic1 = keccak256(abi.encode(payload));

        assertEq(logs[0].topics[0], expectedTopic0);
        assertEq(logs[0].topics[1], expectedTopic1);
    }

    function testIndexedDynamicStaticTupleArrayTopicUsesInPlaceElementEncoding() public {
        StaticTupleParity[] memory payload = new StaticTupleParity[](2);
        payload[0] = StaticTupleParity({amount: 101, recipient: address(0x1111)});
        payload[1] = StaticTupleParity({amount: 202, recipient: address(0x2222)});

        vm.recordLogs();
        emitter.emitIndexedDynamicStaticTupleArray(payload);

        Vm.Log[] memory logs = vm.getRecordedLogs();
        assertEq(logs.length, 1);
        assertEq(logs[0].topics.length, 2);

        bytes32 expectedTopic0 = keccak256(bytes("IndexedDynamicStaticTupleArray((uint256,address)[])"));
        bytes32 expectedTopic1 = keccak256(
            abi.encode(
                payload[0].amount,
                payload[0].recipient,
                payload[1].amount,
                payload[1].recipient
            )
        );

        assertEq(logs[0].topics[0], expectedTopic0);
        assertEq(logs[0].topics[1], expectedTopic1);
    }

    function testIndexedDynamicStaticFixedArrayTopicUsesInPlaceElementEncoding() public {
        address[2][] memory payload = new address[2][](2);
        payload[0] = [address(0x1111), address(0x2222)];
        payload[1] = [address(0x3333), address(0x4444)];

        vm.recordLogs();
        emitter.emitIndexedDynamicStaticFixedArray(payload);

        Vm.Log[] memory logs = vm.getRecordedLogs();
        assertEq(logs.length, 1);
        assertEq(logs[0].topics.length, 2);

        bytes32 expectedTopic0 = keccak256(bytes("IndexedDynamicStaticFixedArray(address[2][])"));
        bytes32 expectedTopic1 = keccak256(
            abi.encode(
                payload[0][0],
                payload[0][1],
                payload[1][0],
                payload[1][1]
            )
        );

        assertEq(logs[0].topics[0], expectedTopic0);
        assertEq(logs[0].topics[1], expectedTopic1);
    }

    function testIndexedDynamicUintArrayTopicUsesInPlaceElementEncoding() public {
        uint256[] memory payload = new uint256[](3);
        payload[0] = 100;
        payload[1] = 200;
        payload[2] = 300;

        vm.recordLogs();
        emitter.emitIndexedDynamicUintArray(payload);

        Vm.Log[] memory logs = vm.getRecordedLogs();
        assertEq(logs.length, 1);
        assertEq(logs[0].topics.length, 2);

        bytes32 expectedTopic0 = keccak256(bytes("IndexedDynamicUintArray(uint256[])"));
        bytes32 expectedTopic1 = keccak256(abi.encode(payload[0], payload[1], payload[2]));

        assertEq(logs[0].topics[0], expectedTopic0);
        assertEq(logs[0].topics[1], expectedTopic1);
    }

    function testIndexedDynamicAddressArrayTopicUsesInPlaceElementEncoding() public {
        address[] memory payload = new address[](3);
        payload[0] = address(0x1111);
        payload[1] = address(0x2222);
        payload[2] = address(0x3333);

        vm.recordLogs();
        emitter.emitIndexedDynamicAddressArray(payload);

        Vm.Log[] memory logs = vm.getRecordedLogs();
        assertEq(logs.length, 1);
        assertEq(logs[0].topics.length, 2);

        bytes32 expectedTopic0 = keccak256(bytes("IndexedDynamicAddressArray(address[])"));
        bytes32 expectedTopic1 = keccak256(abi.encode(payload[0], payload[1], payload[2]));

        assertEq(logs[0].topics[0], expectedTopic0);
        assertEq(logs[0].topics[1], expectedTopic1);
    }

    function testIndexedDynamicBytes32ArrayTopicUsesInPlaceElementEncoding() public {
        bytes32[] memory payload = new bytes32[](3);
        payload[0] = keccak256("alpha");
        payload[1] = keccak256("beta");
        payload[2] = keccak256("gamma");

        vm.recordLogs();
        emitter.emitIndexedDynamicBytes32Array(payload);

        Vm.Log[] memory logs = vm.getRecordedLogs();
        assertEq(logs.length, 1);
        assertEq(logs[0].topics.length, 2);

        bytes32 expectedTopic0 = keccak256(bytes("IndexedDynamicBytes32Array(bytes32[])"));
        bytes32 expectedTopic1 = keccak256(abi.encode(payload[0], payload[1], payload[2]));

        assertEq(logs[0].topics[0], expectedTopic0);
        assertEq(logs[0].topics[1], expectedTopic1);
    }

    function testIndexedDynamicBoolArrayTopicUsesInPlaceElementEncoding() public {
        bool[] memory payload = new bool[](4);
        payload[0] = true;
        payload[1] = false;
        payload[2] = true;
        payload[3] = true;

        vm.recordLogs();
        emitter.emitIndexedDynamicBoolArray(payload);

        Vm.Log[] memory logs = vm.getRecordedLogs();
        assertEq(logs.length, 1);
        assertEq(logs[0].topics.length, 2);

        bytes32 expectedTopic0 = keccak256(bytes("IndexedDynamicBoolArray(bool[])"));
        bytes32 expectedTopic1 = keccak256(abi.encode(payload[0], payload[1], payload[2], payload[3]));

        assertEq(logs[0].topics[0], expectedTopic0);
        assertEq(logs[0].topics[1], expectedTopic1);
    }

    function testUnindexedStaticTupleDataUsesInPlaceEncoding() public {
        StaticTupleParity memory payload = StaticTupleParity({
            amount: 321,
            recipient: address(0x1234)
        });

        vm.recordLogs();
        emitter.emitUnindexedStaticTuple(payload);

        Vm.Log[] memory logs = vm.getRecordedLogs();
        assertEq(logs.length, 1);
        assertEq(logs[0].topics.length, 1);

        bytes32 expectedTopic0 = keccak256(bytes("UnindexedStaticTuple((uint256,address))"));
        bytes memory expectedData = abi.encode(payload.amount, payload.recipient);

        assertEq(logs[0].topics[0], expectedTopic0);
        assertEq(logs[0].data, expectedData);
    }

    function testUnindexedDynamicStaticTupleArrayDataUsesAbiTailEncoding() public {
        StaticTupleParity[] memory payload = new StaticTupleParity[](2);
        payload[0] = StaticTupleParity({amount: 999, recipient: address(0x1111)});
        payload[1] = StaticTupleParity({amount: 1001, recipient: address(0x2222)});

        vm.recordLogs();
        emitter.emitUnindexedDynamicStaticTupleArray(payload);

        Vm.Log[] memory logs = vm.getRecordedLogs();
        assertEq(logs.length, 1);
        assertEq(logs[0].topics.length, 1);

        bytes32 expectedTopic0 = keccak256(bytes("UnindexedDynamicStaticTupleArray((uint256,address)[])"));
        bytes memory expectedData = abi.encode(payload);

        assertEq(logs[0].topics[0], expectedTopic0);
        assertEq(logs[0].data, expectedData);
    }

    function testUnindexedDynamicUintArrayDataUsesAbiTailEncoding() public {
        uint256[] memory payload = new uint256[](3);
        payload[0] = 111;
        payload[1] = 222;
        payload[2] = 333;

        vm.recordLogs();
        emitter.emitUnindexedDynamicUintArray(payload);

        Vm.Log[] memory logs = vm.getRecordedLogs();
        assertEq(logs.length, 1);
        assertEq(logs[0].topics.length, 1);

        bytes32 expectedTopic0 = keccak256(bytes("UnindexedDynamicUintArray(uint256[])"));
        bytes memory expectedData = abi.encode(payload);

        assertEq(logs[0].topics[0], expectedTopic0);
        assertEq(logs[0].data, expectedData);
    }

    function testUnindexedStaticFixedArrayDataUsesInPlaceEncoding() public {
        uint256[2] memory payload = [uint256(111), uint256(222)];

        vm.recordLogs();
        emitter.emitUnindexedStaticFixedArray(payload);

        Vm.Log[] memory logs = vm.getRecordedLogs();
        assertEq(logs.length, 1);
        assertEq(logs[0].topics.length, 1);

        bytes32 expectedTopic0 = keccak256(bytes("UnindexedStaticFixedArray(uint256[2])"));
        bytes memory expectedData = abi.encode(payload);

        assertEq(logs[0].topics[0], expectedTopic0);
        assertEq(logs[0].data, expectedData);
    }

    function testUnindexedDynamicBytes32ArrayDataUsesAbiTailEncoding() public {
        bytes32[] memory payload = new bytes32[](3);
        payload[0] = keccak256("x");
        payload[1] = keccak256("y");
        payload[2] = keccak256("z");

        vm.recordLogs();
        emitter.emitUnindexedDynamicBytes32Array(payload);

        Vm.Log[] memory logs = vm.getRecordedLogs();
        assertEq(logs.length, 1);
        assertEq(logs[0].topics.length, 1);

        bytes32 expectedTopic0 = keccak256(bytes("UnindexedDynamicBytes32Array(bytes32[])"));
        bytes memory expectedData = abi.encode(payload);

        assertEq(logs[0].topics[0], expectedTopic0);
        assertEq(logs[0].data, expectedData);
    }

    function testUnindexedDynamicAddressArrayDataUsesAbiTailEncoding() public {
        address[] memory payload = new address[](3);
        payload[0] = address(0xAAAA);
        payload[1] = address(0xBBBB);
        payload[2] = address(0xCCCC);

        vm.recordLogs();
        emitter.emitUnindexedDynamicAddressArray(payload);

        Vm.Log[] memory logs = vm.getRecordedLogs();
        assertEq(logs.length, 1);
        assertEq(logs[0].topics.length, 1);

        bytes32 expectedTopic0 = keccak256(bytes("UnindexedDynamicAddressArray(address[])"));
        bytes memory expectedData = abi.encode(payload);

        assertEq(logs[0].topics[0], expectedTopic0);
        assertEq(logs[0].data, expectedData);
    }

    function testUnindexedDynamicBoolArrayDataUsesAbiTailEncoding() public {
        bool[] memory payload = new bool[](4);
        payload[0] = true;
        payload[1] = false;
        payload[2] = true;
        payload[3] = false;

        vm.recordLogs();
        emitter.emitUnindexedDynamicBoolArray(payload);

        Vm.Log[] memory logs = vm.getRecordedLogs();
        assertEq(logs.length, 1);
        assertEq(logs[0].topics.length, 1);

        bytes32 expectedTopic0 = keccak256(bytes("UnindexedDynamicBoolArray(bool[])"));
        bytes memory expectedData = abi.encode(payload);

        assertEq(logs[0].topics[0], expectedTopic0);
        assertEq(logs[0].data, expectedData);
    }

    function testUnindexedDynamicStaticFixedArrayDataUsesAbiTailEncoding() public {
        address[2][] memory payload = new address[2][](2);
        payload[0] = [address(0x1111), address(0x2222)];
        payload[1] = [address(0x3333), address(0x4444)];

        vm.recordLogs();
        emitter.emitUnindexedDynamicStaticFixedArray(payload);

        Vm.Log[] memory logs = vm.getRecordedLogs();
        assertEq(logs.length, 1);
        assertEq(logs[0].topics.length, 1);

        bytes32 expectedTopic0 = keccak256(bytes("UnindexedDynamicStaticFixedArray(address[2][])"));
        bytes memory expectedData = abi.encode(payload);

        assertEq(logs[0].topics[0], expectedTopic0);
        assertEq(logs[0].data, expectedData);
    }
}
