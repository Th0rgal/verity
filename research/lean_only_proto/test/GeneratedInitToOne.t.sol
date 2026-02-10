// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "./GeneratedBase.t.sol";

contract GeneratedInitToOneTest is GeneratedBase {
    function testInitToOne() public {
        bytes memory creation = _readHexFile("out/example.creation.bin");
        address deployed = _deploy(creation);

        bytes4 selInitToOne = 0x1ebe7f68;
        bytes4 selGet = 0x7eba7ba6;

        (bool ok,) = deployed.call(abi.encodeWithSelector(selInitToOne, 20));
        require(ok, "initToOne failed (first init)");

        bytes memory data;
        (ok, data) = deployed.call(abi.encodeWithSelector(selGet, 20));
        require(ok, "getSlot failed (slot 20)");
        uint256 val = abi.decode(data, (uint256));
        require(val == 1, "unexpected initToOne value");

        (ok,) = deployed.call(abi.encodeWithSelector(selInitToOne, 20));
        require(!ok, "initToOne should revert when slot already set");
    }
}
