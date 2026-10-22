//! Process-local, bounded cache of complete successful upload builds. Keys
//! retain exact request bytes; fingerprints alone never equate two requests.
use std::collections::VecDeque;
use std::sync::{Arc, Mutex};

pub(super) struct UploadCache {
    entries: Mutex<VecDeque<(String, Arc<String>)>>,
}

impl UploadCache {
    pub fn new() -> Self {
        Self {
            entries: Mutex::new(VecDeque::new()),
        }
    }

    pub fn get(&self, key: &str) -> Option<Arc<String>> {
        self.entries
            .lock()
            .ok()?
            .iter()
            .find(|(stored, _)| stored == key)
            .map(|(_, json)| Arc::clone(json))
    }

    pub fn insert(&self, key: String, json: Arc<String>) {
        const CAPACITY: usize = 64 * 1024 * 1024;
        let size = key.len() + json.len();
        if size > CAPACITY / 2 {
            return;
        }
        let Ok(mut entries) = self.entries.lock() else {
            return;
        };
        entries.retain(|(stored, _)| stored != &key);
        let mut used = entries
            .iter()
            .map(|(key, json)| key.len() + json.len())
            .sum::<usize>();
        while used + size > CAPACITY {
            if let Some((key, json)) = entries.pop_front() {
                used -= key.len() + json.len();
            }
        }
        entries.push_back((key, json));
    }
}

pub(super) struct UploadBuild {
    pub json: Arc<String>,
    pub cache_status: String,
}

impl UploadBuild {
    pub fn new(json: Arc<String>, cache_status: &str) -> Self {
        Self {
            json,
            cache_status: cache_status.into(),
        }
    }
}
