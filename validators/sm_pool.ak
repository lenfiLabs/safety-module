use aada/types.{AssetClass}
use aada/types/pool
use aada/types/pool_stake
use aiken/dict
use aiken/list
use aiken/math/rational
use aiken/transaction.{
  InlineDatum, Input, Mint, Output, OutputReference, Publish, ScriptContext,
  Spend, Transaction,
}
use aiken/transaction/certificate.{CredentialDelegation}
use aiken/transaction/credential.{Address, Inline, ScriptCredential}
use aiken/transaction/value.{
  AssetName, PolicyId, flatten, from_asset, from_minted_value, merge,
  quantity_of, tokens, without_lovelace,
}

pub type Datum {
  params: Constants,
  balance: Int,
  total_lp_tokens: Int,
}

pub type Constants {
  deposit_cs: AssetClass,
  oracle_loan_asset: AssetClass,
  lp_token: AssetClass,
  pool_config_assetname: AssetName,
  pool_nft_name: AssetName,
}

pub type Redeemer {
  action: ContinuingAction,
  config_ref: OutputReference,
}

pub type ContinuingAction {
  LpAdjust { value_delta: Int, continuing_output: Int }
  PayFee { fee: Int, continuing_output: Int }
}

pub type Config {
  pool_fee: Int,
  min_fee: Int,
}

pub type WithdrawalAction {
  ExactWithdrawal
  SwapWithdrawal
}

// Safety module liquidity pool.
// Pool utilizes existing LP token standard to track ownership of pool.

// TODO:
// - Capture Loan repayment redeemer and it's real value (collateral - debt)
// - Withdrawals must be delayd by X days

validator(pool_config_script_hash: PolicyId) {
  fn spend(datum: Datum, redeemer: Redeemer, ctx: ScriptContext) {
    let Datum { params, balance, total_lp_tokens } = datum

    let ScriptContext {
      transaction: Transaction { inputs, mint, reference_inputs, outputs, .. },
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

    let Redeemer { action, config_ref } = redeemer
    expect Some(config_input) =
      list.find(
        reference_inputs,
        fn(inp) -> Bool { inp.output_reference == config_ref },
      )
    let config_has_nft =
      quantity_of(
        config_input.output.value,
        pool_config_script_hash,
        params.pool_config_assetname,
      ) == 1

    expect InlineDatum(raw_config_input_datum) = config_input.output.datum
    expect Config { pool_fee, min_fee }: Config = raw_config_input_datum

    let validate_transition =
      fn(pool_output: Int, f_delta: fn(Int, Int) -> Bool) -> Bool {
        expect Some(pool_output) = outputs |> list.at(pool_output)
        expect InlineDatum(contract_datum) = pool_output.datum
        expect Datum {
          params: output_params,
          balance: output_balance,
          total_lp_tokens: output_total_lp_tokens,
        }: Datum = contract_datum
        let expected_change_value =
          from_asset(
            params.deposit_cs.policy_id,
            params.deposit_cs.asset_name,
            output_balance - balance,
          )
        let expected_value_with_input =
          merge(pool_input_value, expected_change_value)

        let dust_attack_check =
          without_lovelace(expected_value_with_input) == without_lovelace(
            pool_output.value,
          )

        let valid_pool_output_address = pool_output.address == this_address
        let output_is_positive = and {
            output_balance >= 0,
            output_total_lp_tokens >= 0,
          }

        let value_change_check =
          quantity_of(
            expected_value_with_input,
            params.deposit_cs.policy_id,
            params.deposit_cs.asset_name,
          ) == quantity_of(
            pool_output.value,
            params.deposit_cs.policy_id,
            params.deposit_cs.asset_name,
          )
        let pool_input_nft_check =
          quantity_of(pool_input_value, pool_nft_policy, params.pool_nft_name) == 1

        let pool_output_nft_check =
          quantity_of(pool_output.value, pool_nft_policy, params.pool_nft_name) == 1

        let valid_pool_token_tx = pool_output_nft_check && pool_input_nft_check

        let params_check = output_params == params
        let f_delta_check =
          f_delta(
            output_balance - balance,
            output_total_lp_tokens - total_lp_tokens,
          )
        and {
          valid_pool_token_tx?,
          value_change_check?,
          f_delta_check?,
          params_check?,
          output_is_positive?,
          dust_attack_check?,
          valid_pool_output_address?,
        }
      }
    when action is {
      LpAdjust { value_delta, continuing_output } -> {
        let lp_token_delta =
          quantity_of(
            mint,
            params.lp_token.policy_id,
            params.lp_token.asset_name,
          )
        expect Some(owned_proportion) =
          lp_token_delta * balance
            |> rational.new(total_lp_tokens)

        let sign_check = or {
            and {
              value_delta < 0,
              lp_token_delta < 0,
              lp_token_delta < total_lp_tokens,
            },
            and {
              value_delta > 0,
              lp_token_delta > 0,
            },
          }
        let notzero =
          rational.compare(owned_proportion, rational.from_int(0)) != Equal

        let check_delta_amount =
          if value_delta < 0 {
            rational.truncate(owned_proportion) >= value_delta
          } else {
            rational.truncate(owned_proportion) <= value_delta
          }

        let value_delta_check = and {
            sign_check,
            notzero,
          }
        let transition_validator =
          fn(balance_delta, lent_delta, tokens_delta) { and {
              balance_delta == pool_fee + value_delta,
              lent_delta == 0,
              tokens_delta == lp_token_delta,
            } }
        let valid_transition =
          continuing_output
            |> validate_transition(transition_validator)

        and {
          check_delta_amount?,
          valid_transition?,
          value_delta_check?,
          config_has_nft?,
        }
      }
      PayFee { fee, continuing_output } -> {
        let valid_minimum_amount = fee > min_fee
        let transition_validator =
          fn(balance_delta, lent_value_delta, tokens_mint_delta) { and {
              balance_delta == fee,
              lent_value_delta == 0,
              tokens_mint_delta == 0,
            } }
        let valid_transition =
          continuing_output
            |> validate_transition(transition_validator)
        and {
          valid_minimum_amount?,
          valid_transition?,
          config_has_nft?,
        }
      }
    }
  }

  fn mint(redeemer: pool.PoolNFTAction, ctx: ScriptContext) -> Bool {
    let ScriptContext {
      transaction: Transaction { outputs, mint, redeemers, .. },
      purpose,
    } = ctx

    expect Mint(own_script) = purpose
    let pool_control_credential = ScriptCredential(own_script)
    let mint = from_minted_value(mint)

    when redeemer is {
      pool.MintPoolNFT(pool_mint_details) -> {
        let pool_mint_details: pool.PoolCreateDetails = pool_mint_details
        let pool_output =
          outputs
            |> list.at(pool_mint_details.output_index)
        expect Some(Output {
          address: Address(out_credential, Some(out_stake_credential)),
          value,
          ..
        }) = pool_output
        expect Inline(stake_cred) = out_stake_credential
        expect ScriptCredential(stake_hash) = stake_cred

        expect Some(stake_validator_redeemer) =
          dict.get(
            redeemers,
            Publish(
              CredentialDelegation(
                out_stake_credential,
                pool_mint_details.initial_pool_delegation,
              ),
            ),
          )
        expect withdraw_validator_redeemer: pool_stake.StakeRedeemer =
          stake_validator_redeemer

        expect pool_stake.CreatePool(_withdraw_validator_oref) =
          withdraw_validator_redeemer
        let correct_credential = out_credential == pool_control_credential
        // Pool NFT name is stake_hash
        let correct_quantity_output =
          quantity_of(value, own_script, stake_hash) == 1

        expect [(_stake_hash, 1)] = tokens(mint, own_script) |> dict.to_list

        let no_dust_attack =
          when flatten(value) is {
            [(_, _, _)] -> True
            [(_, _, _), (_, _, _)] -> True
            [(_, _, _), (_, _, _), (_, _, _)] -> True
            _ -> False
          }
        and {
          correct_credential,
          correct_quantity_output,
          no_dust_attack,
        }
      }

      // Pool NFT is locked in Pool Validator. You can't easily burn it.
      // Should expect only one policy mint and it's -1
      pool.BurnPoolNFT(burn_tn) -> {
        expect [(burnt_nft_name, -1)] =
          dict.to_list(value.tokens(mint, own_script))
        burn_tn == burnt_nft_name
      }
    }
  }
}
