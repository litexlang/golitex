#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum OutputLanguage {
    English,
    SimplifiedChinese,
    TraditionalChinese,
    Japanese,
    Korean,
    Spanish,
    French,
    German,
    Portuguese,
    Russian,
    Arabic,
    Hindi,
    Vietnamese,
    Indonesian,
}

impl OutputLanguage {
    pub fn supported_codes_text() -> String {
        "en, zh, zh-Hans, ja, ko, es, fr, de, pt, ru, ar, hi, vi, id".to_string()
    }

    pub fn from_cli_lang(value: &str) -> Result<Self, String> {
        match value {
            "en" => Ok(OutputLanguage::English),
            "zh" => Ok(OutputLanguage::SimplifiedChinese),
            "zh-Hans" => Ok(OutputLanguage::TraditionalChinese),
            "ja" => Ok(OutputLanguage::Japanese),
            "ko" => Ok(OutputLanguage::Korean),
            "es" => Ok(OutputLanguage::Spanish),
            "fr" => Ok(OutputLanguage::French),
            "de" => Ok(OutputLanguage::German),
            "pt" => Ok(OutputLanguage::Portuguese),
            "ru" => Ok(OutputLanguage::Russian),
            "ar" => Ok(OutputLanguage::Arabic),
            "hi" => Ok(OutputLanguage::Hindi),
            "vi" => Ok(OutputLanguage::Vietnamese),
            "id" => Ok(OutputLanguage::Indonesian),
            _ => Err(format!(
                "unsupported output language `{}`; expected one of: {}",
                value,
                OutputLanguage::supported_codes_text()
            )),
        }
    }
}
