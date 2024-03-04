use aada/finance
use aada/nft.{CollateralNFTRedeemerLists, MintNFTElem}
use aada/types/pool
use aada/types/pool_stake
use aiken/dict
use aiken/list
use aiken/math/rational
use aiken/transaction.{
  InlineDatum, Input, Mint, Output, Publish, ScriptContext, Spend, Transaction,
}
use aiken/transaction/certificate.{CredentialDelegation}
use aiken/transaction/credential.{Address, Inline, ScriptCredential}
use aiken/transaction/value.{
  PolicyId, flatten, from_asset, from_minted_value, merge, quantity_of, tokens,
  without_lovelace,
}

// This is placeholder contract. That will be used to build safety module on.
validator(delegator_nft_policy: PolicyId, pool_config_script_hash: PolicyId) {
  fn spend(datum: pool.Datum, redeemer: pool.Redeemer, ctx: ScriptContext) {
    let pool.Datum { params, balance, lent_out, total_lp_tokens } = datum
    let ScriptContext {
      transaction: Transaction {
        inputs,
        mint,
        redeemers,
        reference_inputs,
        outputs,
        ..
      },
      purpose,
    } = ctx
    let mint = from_minted_value(mint)
    expect Spend(output_ref) = purpose
    expect Some(Input {
      output: Output { address: this_address, value: pool_input_value, .. },
      ..
    }) =
      list.find(inputs, fn(inp) -> Bool { inp.output_reference == output_ref })
    expect ScriptCredential(this_script_hash) = this_address.payment_credential
    let pool_nft_policy: PolicyId = this_script_hash
    let pool_nft = MintNFTElem {
      policy: pool_nft_policy,
      name: "Pool NFT",
      value: 1,
    }
  }
}