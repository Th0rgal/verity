// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "./GeneratedBase.t.sol";

contract GeneratedMaxStoreTest is GeneratedBase {
    function testMaxStore() public {
        bytes memory creation = _readHexFile("out/example.creation.bin");
        address deployed = _deploy(creation);

        bytes4 selMax = 0xb61d4088;
        bytes4 selGet = 0x7eba7ba6;

        (bool ok,) = deployed.call(abi.encodeWithSelector(selMax, 5, 10, 7));
        require(ok, "maxStore failed (a > b)");

        bytes memory data;
        (ok, data) = deployed.call(abi.encodeWithSelector(selGet, 5));
        require(ok, "getSlot failed (slot 5)");
        uint256 val = abi.decode(data, (uint256));
        require(val == 10, "unexpected maxStore value (slot 5)");

        (ok,) = deployed.call(abi.encodeWithSelector(selMax, 6, 3, 9));
        require(ok, "maxStore failed (b >= a)");

        (ok, data) = deployed.call(abi.encodeWithSelector(selGet, 6));
        require(ok, "getSlot failed (slot 6)");
        val = abi.decode(data, (uint256));
        require(val == 9, "unexpected maxStore value (slot 6)");
    }
}
