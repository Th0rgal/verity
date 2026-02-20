// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

type Wad is uint256;

enum Stage {
    Init,
    Done
}

contract Recipient {}

struct LedgerEntry {
    uint256 amount;
    Stage stage;
    Recipient recipient;
}

struct Envelope {
    LedgerEntry entry;
    Wad total;
}

struct MarketParams {
    address loanToken;
    address collateralToken;
    address oracle;
    address irm;
    uint256 lltv;
}

struct DynamicTuple {
    uint256 amount;
    bytes payload;
}

contract SelectorFixtures {
    event CreateMarket(bytes32 indexed id, MarketParams market);
    event CompositeEvent(bytes32 indexed id, DynamicTuple payload, uint256[] values, bytes note);

    // Parser guard: this commented signature must not be treated as real.
    // function commentedOut(uint256 x) external pure returns (uint256) { return x; }
    /*
      function alsoCommented(address who) external returns (bool) {
          return who != address(0);
      }
    */

    function balanceOf(address account) external view returns (uint256) {
        return account == address(0) ? 0 : 1;
    }

    function transfer(address to, uint256 amount) external returns (bool) {
        return to != address(0) && amount > 0;
    }

    function approve(address spender, uint256 amount) external returns (bool) {
        return spender != address(0) && amount > 0;
    }

    function mint(address to, uint256 amount) external returns (bool) {
        return to != address(0) && amount > 0;
    }

    function burn(address from, uint256 amount) external returns (bool) {
        return from != address(0) && amount > 0;
    }

    function transferBatch(
        address[] calldata recipients,
        uint256[] calldata amounts
    ) external pure returns (uint256) {
        return recipients.length + amounts.length;
    }

    function setRoots(bytes32[2] calldata roots) external pure returns (bytes32) {
        return roots[0];
    }

    function submit(bytes calldata blob) external pure returns (uint256) {
        string memory debugText =
            "function looksLikeSignature(bytes32 x) external pure returns (uint256)";
        if (bytes(debugText).length == 0) {
            return 0;
        }
        return blob.length;
    }

    function callWithCallback(
        function(uint256) external returns (uint256) cb
    ) external pure returns (bool) {
        return cb.address != address(0);
    }

    function canonicalAliases(
        Recipient recipient,
        Wad amount,
        Stage stage,
        uint count,
        int delta
    ) external pure returns (bool) {
        return address(recipient) != address(0)
            || Wad.unwrap(amount) > 0
            || uint8(stage) > 0
            || count > 0
            || delta > 0;
    }

    function canonicalStructs(Envelope calldata env, LedgerEntry[] calldata entries)
        external
        pure
        returns (bool)
    {
        return Wad.unwrap(env.total) > 0 || entries.length > 0;
    }

    function delayedVisibility(uint256 amount)
        virtual
        public
        pure
        returns (uint256)
    {
        return amount;
    }

    // These are intentionally non-selector visibilities and must be ignored by
    // fixture extraction because solc --hashes does not emit them.
    function helperInternal(uint256 amount) internal pure returns (uint256) {
        return amount + 1;
    }

    function helperPrivate(uint256 amount) private pure returns (uint256) {
        return amount + 2;
    }
}

contract SelectorFixturesCollisionEvent {
    // Cross-contract function/event signature reuse is legal and should remain
    // unambiguous in the checker keyspace (`function` vs `event`).
    event MirrorMarket(bytes32 indexed id, MarketParams market);
}

contract SelectorFixturesCollisionFunction {
    function MirrorMarket(bytes32 id, MarketParams calldata market)
        external
        pure
        returns (uint256)
    {
        return uint256(id) + market.lltv;
    }
}
