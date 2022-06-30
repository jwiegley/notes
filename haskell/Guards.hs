{------------------------------------------------------------------------
 - Guards
 -
 - Guards are pure; they get stored in the database, but cannot access the
 - database -- unlike capabilities.
 -
 - Pact has different levels of purity that are not available to userland.
 -
 - A keyset is a highly stylized predicate that does stuff that must remain
 - entirely opaque to the user.
 ------------------------------------------------------------------------}

data KeySet = KeySet

-- PactCapability

--   ModuleCapability :: special cap to install/upgrade a module,
--     transaction-wide, and to directly write to tables. It runs once and
--     only once whenever one of these privileged operations is performed.
--     There are bootstrapping problems with module governance.

--     UserCapability

data Guard
  = KeyGuard KeySet
  | ModuleGuard {- TO BE MADE OBSOLETE BY CAPABILITIES -}
  | PactGuard {- TO BE MADE OBSOLETE BY CAPABILITIES -}
  | UserGuard
    -- | Ensure that a given capability is in scope. These are the arguments
    --   for a call to require-capability.
  | CapabilityGuard String PactValue

{------------------------------------------------------------------------
 - Key sets
 ------------------------------------------------------------------------}

