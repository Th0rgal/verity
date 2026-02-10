// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "./GeneratedBase.t.sol";

contract GeneratedSetIfGreaterTest is GeneratedBase {
    function testSetIfGreater() public {
        bytes memory creation = _readHexFile("out/example.creation.bin");
        address deployed = _deploy(creation);

        bytes4 selSet = 0x2dbeb1ba;
        bytes4 selGet = 0x7eba7ba6;

        (bool ok,) = deployed.call(abi.encodeWithSelector(selSet, 11, 10, 5));
        require(ok, "setIfGreater failed (value > min)");

        bytes memory data;
        (ok, data) = deployed.call(abi.encodeWithSelector(selGet, 11));
        require(ok, "getSlot failed (slot 11)");
        uint256 val = abi.decode(data, (uint256));
        require(val == 10, "unexpected setIfGreater value");

        (ok,) = deployed.call(abi.encodeWithSelector(selSet, 12, 4, 9));
        require(!ok, "setIfGreater should revert when value <= min");
    }
}
