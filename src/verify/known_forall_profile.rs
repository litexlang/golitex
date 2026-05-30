use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::OnceLock;

static PROFILE_ENABLED: OnceLock<bool> = OnceLock::new();

static ENTRIES: AtomicU64 = AtomicU64::new(0);
static SUCCESSES: AtomicU64 = AtomicU64::new(0);
static UNKNOWNS: AtomicU64 = AtomicU64::new(0);
static CANDIDATE_ATTEMPTS: AtomicU64 = AtomicU64::new(0);
static EXACT_CANDIDATE_ATTEMPTS: AtomicU64 = AtomicU64::new(0);
static FALLBACK_CANDIDATE_ATTEMPTS: AtomicU64 = AtomicU64::new(0);
static OTHER_CANDIDATE_ATTEMPTS: AtomicU64 = AtomicU64::new(0);
static BUILTIN_CANDIDATE_ATTEMPTS: AtomicU64 = AtomicU64::new(0);
static USER_CANDIDATE_ATTEMPTS: AtomicU64 = AtomicU64::new(0);
static ARG_MATCHES: AtomicU64 = AtomicU64::new(0);
static REQUIREMENT_FAILURES: AtomicU64 = AtomicU64::new(0);

#[derive(Clone, Copy, Default)]
pub struct KnownForallProfileSnapshot {
    pub entries: u64,
    pub successes: u64,
    pub unknowns: u64,
    pub candidate_attempts: u64,
    pub exact_candidate_attempts: u64,
    pub fallback_candidate_attempts: u64,
    pub other_candidate_attempts: u64,
    pub builtin_candidate_attempts: u64,
    pub user_candidate_attempts: u64,
    pub arg_matches: u64,
    pub requirement_failures: u64,
}

#[derive(Clone, Copy)]
pub(crate) enum KnownForallSearchPhase {
    ExactShape,
    Fallback,
    OtherShape,
}

#[derive(Clone, Copy)]
pub(crate) enum KnownForallEnvKind {
    Builtin,
    User,
}

pub fn enabled() -> bool {
    *PROFILE_ENABLED.get_or_init(|| std::env::var_os("LITEX_PROFILE_KNOWN_FORALL").is_some())
}

pub fn reset() {
    if !enabled() {
        return;
    }
    ENTRIES.store(0, Ordering::Relaxed);
    SUCCESSES.store(0, Ordering::Relaxed);
    UNKNOWNS.store(0, Ordering::Relaxed);
    CANDIDATE_ATTEMPTS.store(0, Ordering::Relaxed);
    EXACT_CANDIDATE_ATTEMPTS.store(0, Ordering::Relaxed);
    FALLBACK_CANDIDATE_ATTEMPTS.store(0, Ordering::Relaxed);
    OTHER_CANDIDATE_ATTEMPTS.store(0, Ordering::Relaxed);
    BUILTIN_CANDIDATE_ATTEMPTS.store(0, Ordering::Relaxed);
    USER_CANDIDATE_ATTEMPTS.store(0, Ordering::Relaxed);
    ARG_MATCHES.store(0, Ordering::Relaxed);
    REQUIREMENT_FAILURES.store(0, Ordering::Relaxed);
}

pub fn snapshot() -> KnownForallProfileSnapshot {
    KnownForallProfileSnapshot {
        entries: ENTRIES.load(Ordering::Relaxed),
        successes: SUCCESSES.load(Ordering::Relaxed),
        unknowns: UNKNOWNS.load(Ordering::Relaxed),
        candidate_attempts: CANDIDATE_ATTEMPTS.load(Ordering::Relaxed),
        exact_candidate_attempts: EXACT_CANDIDATE_ATTEMPTS.load(Ordering::Relaxed),
        fallback_candidate_attempts: FALLBACK_CANDIDATE_ATTEMPTS.load(Ordering::Relaxed),
        other_candidate_attempts: OTHER_CANDIDATE_ATTEMPTS.load(Ordering::Relaxed),
        builtin_candidate_attempts: BUILTIN_CANDIDATE_ATTEMPTS.load(Ordering::Relaxed),
        user_candidate_attempts: USER_CANDIDATE_ATTEMPTS.load(Ordering::Relaxed),
        arg_matches: ARG_MATCHES.load(Ordering::Relaxed),
        requirement_failures: REQUIREMENT_FAILURES.load(Ordering::Relaxed),
    }
}

pub(crate) fn record_entry() {
    if enabled() {
        ENTRIES.fetch_add(1, Ordering::Relaxed);
    }
}

pub(crate) fn record_success() {
    if enabled() {
        SUCCESSES.fetch_add(1, Ordering::Relaxed);
    }
}

pub(crate) fn record_unknown() {
    if enabled() {
        UNKNOWNS.fetch_add(1, Ordering::Relaxed);
    }
}

pub(crate) fn record_candidate_attempt(
    phase: KnownForallSearchPhase,
    env_kind: KnownForallEnvKind,
) {
    if !enabled() {
        return;
    }
    CANDIDATE_ATTEMPTS.fetch_add(1, Ordering::Relaxed);
    match phase {
        KnownForallSearchPhase::ExactShape => {
            EXACT_CANDIDATE_ATTEMPTS.fetch_add(1, Ordering::Relaxed);
        }
        KnownForallSearchPhase::Fallback => {
            FALLBACK_CANDIDATE_ATTEMPTS.fetch_add(1, Ordering::Relaxed);
        }
        KnownForallSearchPhase::OtherShape => {
            OTHER_CANDIDATE_ATTEMPTS.fetch_add(1, Ordering::Relaxed);
        }
    }
    match env_kind {
        KnownForallEnvKind::Builtin => {
            BUILTIN_CANDIDATE_ATTEMPTS.fetch_add(1, Ordering::Relaxed);
        }
        KnownForallEnvKind::User => {
            USER_CANDIDATE_ATTEMPTS.fetch_add(1, Ordering::Relaxed);
        }
    }
}

pub(crate) fn record_arg_match() {
    if enabled() {
        ARG_MATCHES.fetch_add(1, Ordering::Relaxed);
    }
}

pub(crate) fn record_requirement_failure() {
    if enabled() {
        REQUIREMENT_FAILURES.fetch_add(1, Ordering::Relaxed);
    }
}
