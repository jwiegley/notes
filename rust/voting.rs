pub type VoterId = u64;

// pub enum Vote {
//     Unspecified,
//     Yes,
//     No,
// }

#[derive(Clone)]
pub struct Tally {
    pub timestamp_seconds: u64,
    pub yes: u64,
    pub no: u64,
    pub total: u64,
}

/// The Voter trait represent an entity with voting power.
pub trait Voter {
    /// Return this voter's current voting power. How this is calculated is up
    /// to the entity, but it should be represented as some equivalent to E8s
    /// in tokens.
    fn voting_power(&self, now_seconds: u64) -> u64;

    /// Grant a voting reward in NS tokens to this voter.
    fn grant_voting_reward(&mut self, reward_tokens: u64);
}

/// Determines several things:
/// - The schedule for when voting rewards are distributed
/// - The pool of rewards to be distributed at those times
/// - The amount of rewards allocated per eligible voter
pub trait Rewards {
    /// Determine when the next voting distribution time will be. Possible
    /// results:
    /// - None: Cannot be determined yet, call again later.
    /// - Some(t | t <= now_seconds): The time has already passed, distribute
    ///   immediately.
    /// - Some(t | t > now_seconds): `t` is a time in the future when rewards
    ///   should be distributed.
    fn next_distribution_time(&self, now_seconds: u64) -> Option<u64>;

    /// Allocate the total amount of reward to be distributed among eligible
    /// voters. Note that this only computes the amount available based on
    /// network parameters; distribution to individual voters is done by
    /// Governance.
    fn distribute_rewards(&self, now_seconds: u64, voters: impl Iterator<Item = VoterId>);
}

/// A Poll for a particular proposal. This is strictly an incrementalization
/// of Polls::determine_vote.
pub trait Poll<Proposal> {
    /// Cast a vote for the given voter, returning the updated Tally. Note
    /// that there could be abstraction behind this voter, such as a Ballot
    /// that remembers their available voting power at the time the poll was
    /// made.
    fn cast_vote(&mut self, now_seconds: u64, voter: VoterId) -> Tally;

    fn is_decided() -> Option<Tally>;
}

pub trait VoterRegistration {
    fn register_voter(&mut self, voter: Box<dyn Voter>) -> VoterId;
    fn unregister_voter(&mut self, voter: VoterId) -> bool;

    fn known_voters(&mut self) -> std::slice::IterMut<'_, &mut Box<dyn Voter>>;

    fn total_voting_power(&self, now_seconds: u64) -> u64;
}

// pub trait SNS {
//     Set<Poll>    database

//     Rewards      algorithm in data
//     VotingPower  algorithm in data
//     Polling      algorithm in data
// }

// pub trait Governance<Proposal> {
//     Set<Neuron>     database
//     Set<Proposals>  database

//     /// Create a poll for a given proposal.
//     fn create_poll(&mut self, now_seconds: u64, proposal: &Proposal) -> Box<dyn Poll<Proposal>> {}
// }
