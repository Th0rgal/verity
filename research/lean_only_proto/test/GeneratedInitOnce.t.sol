// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "./GeneratedBase.t.sol";

contract GeneratedInitOnceTest is GeneratedBase {
    function testInitOnce() public {
        bytes memory creation = _readHexFile("out/example.creation.bin");
        address deployed = _deploy(creation);

        bytes4 selInitOnce = 0xd3b9b05a;
        bytes4 selGet = 0x7eba7ba6;

        (bool ok,) = deployed.call(abi.encodeWithSelector(selInitOnce, 12, 777));
        require(ok, "initOnce failed (first init)");

        bytes memory data;
        (ok, data) = deployed.call(abi.encodeWithSelector(selGet, 12));
        require(ok, "getSlot failed (slot 12)");
        uint256 val = abi.decode(data, (uint256));
        require(val == 777, "unexpected initOnce value");

        (ok,) = deployed.call(abi.encodeWithSelector(selInitOnce, 12, 888));
        require(!ok, "initOnce should revert when slot already set");
    }
}
