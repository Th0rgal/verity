import { readFileSync } from "fs";
import { dirname, join } from "path";
import { fileURLToPath } from "url";
import { bundledLanguages, createHighlighter } from "shiki";

const here = dirname(fileURLToPath(import.meta.url));
const docsRoot = join(here, "..");
const grammar = JSON.parse(readFileSync(join(docsRoot, "syntaxes/verity.tmLanguage.json"), "utf8"));
const theme = JSON.parse(readFileSync(join(docsRoot, "themes/lfglabs-cream.json"), "utf8"));

const sample = `verity_contract UnlinkPool where
  storage
    storage_namespace erc7201 "unlink.storage.State"
    state : StorageStruct [
      nextLeafIndex : Uint256 @word 0,
      verifierRouter : Address @word 10
    ] := slot 0

    storage_namespace erc7201 "unlink.storage.UnlinkPoolRelayers"
    relayersSlot : Address -> Uint256 := slot 0

  linked_externals
    external getCircuit(Address, Uint256) -> (Circuit)
    external getCircuit_try(Address, Uint256) -> (Bool, Circuit)

  modifier onlyRelayer := do
    let sender ← msgSender
    let isR ← getMapping relayersSlot sender
    requireError (isR != 0) PoolUnauthorizedRelayer()

  function nonreentrant(reentrancyLockSlot) transfer
      (transactions : Array Transaction) with onlyRelayer : Unit := do
    let txLen := arrayLength transactions
    requireError (txLen != 0) PoolEmptyTransactions()
    forEach "i" txLen (do
      let txn := arrayElement transactions i
      let verifierRouter ← getStorageAddr stateVerifierRouter
      let (success, circuit) ← tryExternalCall "getCircuit"
        [verifierRouter, txn.circuitId]
      requireError success PoolCircuitNotRegistered()
      requireError (circuit.verifier != 0) PoolCircuitNotRegistered()
      let (proofOk, ok) ← tryExternalCall "verifySpend"
        [circuit.verifier, abiEncode txn.proof, txn.merkleRoot,
         txn.contextHash, txn.nullifierHashes, txn.newCommitments]
      requireError proofOk PoolProofVerificationFailed()
      requireError ok PoolProofVerificationFailed()
      let leaves ← realCommitments txn.newCommitments maxUint
      let startIndex ← nextLeafIndex
      let newRoot ← insertLeaves leaves
      emit "Transferred"
        [newRoot, startIndex, leaves,
         realNullifiers txn.nullifierHashes, txn.ciphertexts])
`;

const highlighter = await createHighlighter({
  themes: [theme],
  langs: [
    ...Object.keys(bundledLanguages).filter((lang) => lang !== "mermaid"),
    {
      ...grammar,
      name: "verity",
      aliases: ["vty"],
    },
  ],
});

const tokens = highlighter.codeToTokens(sample, {
  lang: "verity",
  theme: "Verity Paper Light",
  includeExplanation: true,
}).tokens.flat();

function scopesFor(content) {
  return tokens.flatMap((token) =>
    token.explanation
      .filter((part) => part.content.trim() === content || part.content.includes(content))
      .flatMap((part) => part.scopes.map((scope) => scope.scopeName))
  );
}

const expectations = [
  ["verity_contract", "keyword.declaration.contract.verity"],
  ["UnlinkPool", "entity.name.type.contract.verity"],
  ["storage", "keyword.other.section.verity"],
  ["storage_namespace", "keyword.other.storage-namespace.verity"],
  ["erc7201", "keyword.other.storage-namespace.kind.verity"],
  ["\"unlink.storage.State\"", "string.quoted.double.storage-namespace.verity"],
  ["state", "variable.other.storage.verity"],
  ["StorageStruct", "storage.type.verity"],
  ["nextLeafIndex", "variable.other.storage.member.verity"],
  ["@word", "keyword.other.word-offset.verity"],
  ["relayersSlot", "variable.other.storage.verity"],
  ["Address", "storage.type.verity"],
  ["Array", "storage.type.verity"],
  ["slot", "keyword.other.slot.verity"],
  ["external", "keyword.declaration.external.verity"],
  ["getCircuit", "entity.name.function.external.verity"],
  ["modifier", "keyword.declaration.modifier.verity"],
  ["onlyRelayer", "entity.name.function.modifier.verity"],
  ["function", "keyword.declaration.function.verity"],
  ["nonreentrant", "storage.modifier.reentrancy.verity"],
  ["transfer", "entity.name.function.verity"],
  ["with", "keyword.control.modifier-clause.verity"],
  ["msgSender", "support.function.context.verity"],
  ["getMapping", "support.function.storage.verity"],
  ["requireError", "support.function.guard.verity"],
  ["arrayLength", "support.function.storage.verity"],
  ["forEach", "support.function.loop.verity"],
  ["tryExternalCall", "support.function.external-call.verity"],
  ["abiEncode", "support.function.abi.verity"],
  ["proof", "variable.other.property.verity"],
  ["PoolCircuitNotRegistered", "entity.name.exception.custom-error.verity"],
  ["emit", "support.function.event.verity"],
  ["\"Transferred\"", "entity.name.function.event.verity"],
];

const failures = expectations.filter(([content, expectedScope]) => {
  const scopes = scopesFor(content);
  return !scopes.includes(expectedScope);
});

if (failures.length > 0) {
  console.error("Verity highlighting scope check failed:");
  for (const [content, expectedScope] of failures) {
    console.error(`- ${content}: expected ${expectedScope}, got ${scopesFor(content).join(", ") || "no token"}`);
  }
  process.exit(1);
}

console.log(`Verified ${expectations.length} Verity syntax highlighting scopes.`);
