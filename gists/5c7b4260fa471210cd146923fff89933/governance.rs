    pub async fn claim_or_refresh_neuron_from_account(
        &mut self,
        caller: &PrincipalId,
        claim_or_refresh: &ClaimOrRefreshNeuronFromAccount,
    ) -> ClaimOrRefreshNeuronFromAccountResponse {
        let controller = claim_or_refresh.controller.unwrap_or(*caller);
        let result = self
            .claim_or_refresh_neuron_from_account_internal(Memo(claim_or_refresh.memo), controller)
            .await;
        match result {
            Ok(neuron_id) => ClaimOrRefreshNeuronFromAccountResponse {
                result: Some(ClaimOrRefreshResult::NeuronId(neuron_id)),
            },
            Err(err) => ClaimOrRefreshNeuronFromAccountResponse {
                result: Some(ClaimOrRefreshResult::Error(err)),
            },
        }
    }

    async fn claim_or_refresh_neuron_from_account_internal(
        &mut self,
        memo: Memo,
        controller: PrincipalId,
    ) -> Result<NeuronId, GovernanceError> {
        // Compute the subaccount we expect the transfer to have been made to.
        let gov_subaccount = compute_neuron_staking_subaccount(controller, memo.0);
        let account = AccountIdentifier::new(GOVERNANCE_CANISTER_ID.get(), Some(gov_subaccount));
        let now = self.env.now();

        // See if there is already a neuron with this subaccount, if there is
        // one refresh the stake of that neuron, if the stake is different from
        // the balance.
        if let Some(neuron) = self.get_neuron_by_subaccount(&gov_subaccount) {
            let nid = neuron.id.as_ref().expect("Neuron must have an id").clone();
            // We need to lock the neuron to make sure it doesn't undergo
            // concurrent changes while we're checking the balance and
            // refreshing the stake.
            let _neuron_lock = self.lock_neuron_for_command(
                nid.id,
                NeuronInFlightCommand {
                    timestamp: self.env.now(),
                    command: Some(InFlightCommand::ClaimOrRefresh(
                        ClaimOrRefreshNeuronFromAccount {
                            controller: Some(controller),
                            memo: memo.0,
                        },
                    )),
                },
            )?;

            // Get the balance of the neuron ledger canister.
            let balance = self.ledger.account_balance(account).await?;
            let neuron = self.get_neuron_mut(&nid)?;
            match neuron.cached_neuron_stake_e8s.cmp(&balance.get_e8s()) {
                Ordering::Greater => {
                    println!(
                        "{}ERROR. Neuron cached stake was inconsistent.\
                          Neuron account: {} has less e8s: {} than the cached neuron stake: {}.\
                          Stake adjusted.",
                        LOG_PREFIX,
                        account,
                        balance.get_e8s(),
                        neuron.cached_neuron_stake_e8s
                    );
                    neuron.cached_neuron_stake_e8s = balance.get_e8s();
                }
                Ordering::Less => {
                    // If the neuron has an age, adjust it.
                    if neuron.aging_since_timestamp_seconds != u64::MAX {
                        // Note that old_stake < new_stake
                        let old_stake = neuron.cached_neuron_stake_e8s as u128;
                        let new_stake = balance.get_e8s() as u128;
                        assert!(new_stake > 0);
                        let old_age =
                            now.saturating_sub(neuron.aging_since_timestamp_seconds) as u128;
                        let new_age = (old_age * old_stake) / new_stake;
                        // new_age * new_stake = old_age * old_stake -
                        // (old_stake * old_age) % new_stake. That is, age is
                        // adjusted in proportion to the stake, but due to the
                        // discrete nature of u64 numbers, some resolution is
                        // lost due to the division above. This means the age
                        // bonus is derived from a constant times age times
                        // stake, minus up to new_stake - 1 each time the
                        // neuron is refreshed. Only if old_age * old_stake is
                        // a multiple of new_stake does the age remain
                        // constant after the refresh operation.
                        neuron.aging_since_timestamp_seconds = now.saturating_sub(new_age as u64);
                        // Note that if new_stake == old_stake, then
                        // new_age == old_age, and
                        // now - new_age =
                        // now-(now-neuron.aging_since_timestamp_seconds)
                        // = neuron.aging_since_timestamp_seconds.
                    }
                    // Update the cached stake - after the age has been adjusted.
                    neuron.cached_neuron_stake_e8s = balance.get_e8s();
                }
                // If the stake is the same as the account balance,
                // just return the neuron id (this way this method
                // also serves the purpose of allowing to discover the
                // neuron id based on the memo and the controller).
                Ordering::Equal => (),
            };

            Ok(nid)
        }
        // If there isn't a neuron already we create one, unless the account
        // doesn't have enough to stake a neuron or we've reached the maximum number
        // of neurons, in which case we return an error.
        // We can't return the funds without more information about the
        // source account, so as a workaround for insufficient stake we can ask the
        // user to transfer however much is missing to stake a neuron and they can
        // then disburse if they so choose. We need to do something more involved
        // if we've reached the max, TODO.
        //
        // Note that we need to create the neuron before checking the balance
        // so that we record the neuron and avoid a race where a user calls
        // this method a second time before the first time responds. If we store
        // the neuron and lock it before we make the call, we know that any
        // competing call will need to wait for this one to finish before
        // proceeding.
        else {
            let nid = self.new_neuron_id();
            let neuron = Neuron {
                id: Some(nid.clone()),
                account: gov_subaccount.to_vec(),
                controller: Some(controller),
                cached_neuron_stake_e8s: 0,
                created_timestamp_seconds: self.env.now(),
                aging_since_timestamp_seconds: self.env.now(),
                dissolve_state: Some(DissolveState::DissolveDelaySeconds(0)),
                transfer: None,
                kyc_verified: true,
                followees: self.proto.default_followees.clone(),
                hot_keys: vec![],
                maturity_e8s_equivalent: 0,
                neuron_fees_e8s: 0,
                not_for_profit: false,
                recent_ballots: vec![],
            };

            // This also verifies that there are not too many neurons already.
            self.add_neuron(nid.id, neuron.clone())?;

            let _neuron_lock = self.lock_neuron_for_command(
                nid.id,
                NeuronInFlightCommand {
                    timestamp: self.env.now(),
                    command: Some(InFlightCommand::ClaimOrRefresh(
                        ClaimOrRefreshNeuronFromAccount {
                            controller: Some(controller),
                            memo: memo.0,
                        },
                    )),
                },
            )?;

            // Get the balance of the neuron ledger canister.
            let balance = self.ledger.account_balance(account).await?;
            let min_stake = self.economics().neuron_minimum_stake_e8s;
            if balance.get_e8s() < min_stake {
                // To prevent this method from creating non-staked
                // neurons, we must also remove the neuron that was
                // previously created.
                self.remove_neuron(nid.id, neuron)?;
                return Err(GovernanceError::new_with_message(
                    ErrorType::InsufficientFunds,
                    format!(
                        "Account does not have enough funds to stake a neuron. \
                         Please make sure that account has at least {:?} e8s (was {:?} e8s)",
                        min_stake,
                        balance.get_e8s()
                    ),
                ));
            }

            // Ok, we were able to stake the neuron.
            match self.get_neuron_mut(&nid) {
                Ok(mut neuron) => {
                    // Adjust the stake.
                    neuron.cached_neuron_stake_e8s = balance.get_e8s();
                    Ok(nid)
                }
                Err(err) => {
                    // This should not be possible, but let's be
                    // defensive and provide a reasonable error message.
                    Err(GovernanceError::new_with_message(
                        ErrorType::NotFound,
                        format!(
                            "When attempting to stake a neuron with ID {:?} and stake {:?},\
			     the neuron disappeared while the operation was in flight.\
			     Please try again: {:?}",
                            nid,
                            balance.get_e8s(),
                            err
                        ),
                    ))
                }
            }
        }
    }
