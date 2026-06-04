# MetaMathQA

Generated arithmetic and algebra QA derivations with explicit intermediate quantities.

Each example below is an independent checked Litex snippet. The metadata record keeps the dataset translation fields next to the runnable code.

## 1. `MetaMathQA-GSM_AnsAug-331903`

```yaml
id: "MetaMathQA-GSM_AnsAug-331903"
source: "MetaMathQA"
topic: "augmented arithmetic and algebra QA"
difficulty: "mixed"
natural_language_idea: "Use the generated QA solution as a Litex arithmetic or algebra derivation with explicit intermediate quantities."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
claim:
    prove:
        forall peppers_per_very_spicy, peppers_per_spicy, peppers_per_mild, previous_vs_count, previous_s_count, previous_m_count, current_s_count, current_m_count, previous_vs_peppers, previous_s_peppers, previous_m_peppers, previous_total, current_s_peppers, current_m_peppers, current_total, fewer N_pos:
            peppers_per_very_spicy = 3
            peppers_per_spicy = 2
            peppers_per_mild = 1
            previous_vs_count = 30
            previous_s_count = 30
            previous_m_count = 10
            current_s_count = 15
            current_m_count = 90
            previous_vs_peppers = previous_vs_count * peppers_per_very_spicy
            previous_s_peppers = previous_s_count * peppers_per_spicy
            previous_m_peppers = previous_m_count * peppers_per_mild
            previous_total = previous_vs_peppers + previous_s_peppers + previous_m_peppers
            current_s_peppers = current_s_count * peppers_per_spicy
            current_m_peppers = current_m_count * peppers_per_mild
            current_total = current_s_peppers + current_m_peppers
            fewer = previous_total - current_total
            =>:
                fewer = 40
    previous_vs_peppers = 30 * 3
    previous_vs_peppers = 90

    previous_s_peppers = 30 * 2
    previous_s_peppers = 60

    previous_m_peppers = 10 * 1
    previous_m_peppers = 10

    previous_total = previous_vs_peppers + previous_s_peppers + previous_m_peppers = (90) + (60) + (10) = 90 + 60 + 10
    previous_total = previous_vs_peppers + previous_s_peppers + previous_m_peppers = (90) + (60) + (10) = 160

    current_s_peppers = 15 * 2
    current_s_peppers = 30

    current_m_peppers = 90 * 1
    current_m_peppers = 90

    current_total = current_s_peppers + current_m_peppers = (30) + (90) = 30 + 90
    current_total = current_s_peppers + current_m_peppers = (30) + (90) = 120

    fewer = previous_total - current_total = (160) - (120) = 160 - 120
    fewer = previous_total - current_total = (160) - (120) = 40
```

## 2. `MetaMathQA-GSM_AnsAug-332159`

```yaml
id: "MetaMathQA-GSM_AnsAug-332159"
source: "MetaMathQA"
topic: "augmented arithmetic and algebra QA"
difficulty: "mixed"
natural_language_idea: "Use the generated QA solution as a Litex arithmetic or algebra derivation with explicit intermediate quantities."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
claim:
    prove:
        forall days_of_protest, cities, protest_days, arrests_per_day, total_arrests, pretrial_days_per_person, total_pretrial_days, week_days, two_week_sentence_weeks, two_week_sentence_days, half_sentence_days, posttrial_days_per_person, total_posttrial_days, total_days, total_weeks N_pos:
            days_of_protest = 30
            cities = 21
            protest_days = days_of_protest * cities
            arrests_per_day = 10
            total_arrests = arrests_per_day * protest_days
            pretrial_days_per_person = 4
            total_pretrial_days = total_arrests * pretrial_days_per_person
            week_days = 7
            two_week_sentence_weeks = 2
            two_week_sentence_days = two_week_sentence_weeks * week_days
            half_sentence_days = two_week_sentence_days / 2
            posttrial_days_per_person = half_sentence_days
            total_posttrial_days = total_arrests * posttrial_days_per_person
            total_days = total_pretrial_days + total_posttrial_days
            total_weeks = total_days / week_days
            =>:
                total_weeks = 9900
    protest_days = 30 * 21
    protest_days = 630

    total_arrests = 10 * 630
    total_arrests = 6300

    total_pretrial_days = 6300 * 4
    total_pretrial_days = 25200

    two_week_sentence_days = 2 * 7
    half_sentence_days = two_week_sentence_days / 2 = (2 * 7) / 2
    half_sentence_days = two_week_sentence_days / 2 = (2 * 7) / 2 = 7

    posttrial_days_per_person = half_sentence_days = (7) = 7
    total_posttrial_days = total_arrests * posttrial_days_per_person = (6300) * (7) = 6300 * 7
    total_posttrial_days = total_arrests * posttrial_days_per_person = (6300) * (7) = 44100

    total_days = total_pretrial_days + total_posttrial_days = (25200) + (44100) = 25200 + 44100
    total_days = total_pretrial_days + total_posttrial_days = (25200) + (44100) = 69300

    total_weeks = 69300 / 7
    total_weeks = 9900
```

## 3. `MetaMathQA-GSM_AnsAug-332216`

```yaml
id: "MetaMathQA-GSM_AnsAug-332216"
source: "MetaMathQA"
topic: "augmented arithmetic and algebra QA"
difficulty: "mixed"
natural_language_idea: "Use the generated QA solution as a Litex arithmetic or algebra derivation with explicit intermediate quantities."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
claim:
    prove:
        forall total_homes, first_num, first_den, first_fraction, homes_first_distributed, homes_remaining_after_first, second_percent, percent_den, second_fraction, homes_distributed_second, homes_remaining R:
            total_homes = 200
            first_num = 2
            first_den = 5
            first_fraction = first_num / first_den
            homes_first_distributed = first_fraction * total_homes
            homes_remaining_after_first = total_homes - homes_first_distributed
            second_percent = 60
            percent_den = 100
            second_fraction = second_percent / percent_den
            homes_distributed_second = second_fraction * homes_remaining_after_first
            homes_remaining = homes_remaining_after_first - homes_distributed_second
            =>:
                homes_remaining = 48
    first_fraction = 2 / 5
    homes_first_distributed = (2 / 5) * 200
    homes_first_distributed = 80

    homes_remaining_after_first = 200 - 80
    homes_remaining_after_first = 120

    second_fraction = 60 / 100
    homes_distributed_second = second_fraction * homes_remaining_after_first = (60 / 100) * (120) = (60 / 100) * 120
    homes_distributed_second = second_fraction * homes_remaining_after_first = (60 / 100) * (120) = 72

    homes_remaining = homes_remaining_after_first - homes_distributed_second = (120) - (72) = 120 - 72
    homes_remaining = homes_remaining_after_first - homes_distributed_second = (120) - (72) = 48
```

## 4. `MetaMathQA-GSM_AnsAug-332445`

```yaml
id: "MetaMathQA-GSM_AnsAug-332445"
source: "MetaMathQA"
topic: "augmented arithmetic and algebra QA"
difficulty: "mixed"
natural_language_idea: "Use the generated QA solution as a Litex arithmetic or algebra derivation with explicit intermediate quantities."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
claim:
    prove:
        forall growth_per_month, months_per_year, growth_per_year, cut_length, remaining_length, growth_per_haircut, haircuts_per_year, haircut_cost, tip_rate, tip_per_haircut, total_per_haircut, total_cost R:
            growth_per_month = 1.5
            months_per_year = 12
            growth_per_year = growth_per_month * months_per_year
            cut_length = 9
            remaining_length = 6
            growth_per_haircut = cut_length - remaining_length
            haircuts_per_year = growth_per_year / growth_per_haircut
            haircut_cost = 45
            tip_rate = 20 / 100
            tip_per_haircut = haircut_cost * tip_rate
            total_per_haircut = haircut_cost + tip_per_haircut
            total_cost = total_per_haircut * haircuts_per_year
            =>:
                total_cost = 324
    growth_per_year = 1.5 * 12
    growth_per_year = 18

    growth_per_haircut = 9 - 6
    growth_per_haircut = 3

    haircuts_per_year = growth_per_year / growth_per_haircut = (18) / (3) = 18 / 3
    haircuts_per_year = growth_per_year / growth_per_haircut = (18) / (3) = 6

    tip_rate = 20 / 100
    tip_rate = 1/5

    tip_per_haircut = 45 * tip_rate
    tip_per_haircut = 45 * (1/5)
    tip_per_haircut = 9

    total_per_haircut = 45 + 9
    total_per_haircut = 54

    total_cost = total_per_haircut * haircuts_per_year = (54) * (6) = 54 * 6
    total_cost = total_per_haircut * haircuts_per_year = (54) * (6) = 324
```

## 5. `MetaMathQA-GSM_AnsAug-350550`

```yaml
id: "MetaMathQA-GSM_AnsAug-350550"
source: "MetaMathQA"
topic: "augmented arithmetic and algebra QA"
difficulty: "mixed"
natural_language_idea: "Use the generated QA solution as a Litex arithmetic or algebra derivation with explicit intermediate quantities."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
claim:
    prove:
        forall w_meat, w_pumpkin, w_cheese R, m_meat, m_pumpkin, m_cheese, b_pumpkin N_pos, javier_meat, javier_pumpkin, javier_cheese, javier_total, brother_total, winner_total R:
            w_meat = 1.5
            w_pumpkin = 1.25
            w_cheese = 1
            m_meat = 5
            m_pumpkin = 2
            m_cheese = 4
            b_pumpkin = 12
            javier_meat = m_meat * w_meat
            javier_pumpkin = m_pumpkin * w_pumpkin
            javier_cheese = m_cheese * w_cheese
            javier_total = javier_meat + javier_pumpkin + javier_cheese
            brother_total = b_pumpkin * w_pumpkin
            winner_total = brother_total
            =>:
                winner_total = 15
    javier_meat = 5 * 1.5
    javier_meat = 7.5

    javier_pumpkin = 2 * 1.25
    javier_pumpkin = 2.5

    javier_cheese = 4 * 1
    javier_cheese = 4

    javier_total = javier_meat + javier_pumpkin + javier_cheese = (7.5) + (2.5) + (4) = 7.5 + 2.5 + 4
    javier_total = javier_meat + javier_pumpkin + javier_cheese = (7.5) + (2.5) + (4) = 14

    brother_total = 12 * 1.25
    brother_total = 15

    winner_total = brother_total
    winner_total = brother_total = (15) = 15
```

## 6. `MetaMathQA-GSM_FOBAR-350665`

```yaml
id: "MetaMathQA-GSM_FOBAR-350665"
source: "MetaMathQA"
topic: "augmented arithmetic and algebra QA"
difficulty: "mixed"
natural_language_idea: "Use the generated QA solution as a Litex arithmetic or algebra derivation with explicit intermediate quantities."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
claim:
    prove:
        forall third_classes, third_size, third_students, fourth_classes, fourth_size, fourth_students, fifth_classes, fifth_size, fifth_students, total_students N_pos, x, burger_cost, carrot_unit, cookie_unit, carrot_cost, cookie_cost, total_cost R:
            third_classes = 5
            third_size = 30
            third_students = third_classes * third_size

            fourth_classes = 4
            fourth_size = 28
            fourth_students = fourth_classes * fourth_size

            fifth_classes = 4
            fifth_size = 27
            fifth_students = fifth_classes * fifth_size

            total_students = third_students + fourth_students + fifth_students

            carrot_unit = 0.5
            cookie_unit = 0.2

            burger_cost = total_students * x
            carrot_cost = total_students * carrot_unit
            cookie_cost = total_students * cookie_unit

            total_cost = burger_cost + carrot_cost + cookie_cost
            total_cost = 1036
            =>:
                x = 2.1
    third_students = 5 * 30
    third_students = 150

    fourth_students = 4 * 28
    fourth_students = 112

    fifth_students = 4 * 27
    fifth_students = 108

    total_students = third_students + fourth_students + fifth_students = (150) + (112) + (108) = 150 + 112 + 108
    total_students = third_students + fourth_students + fifth_students = (150) + (112) + (108) = 370

    burger_cost = total_students * x = (370) * x = 370 * x

    carrot_cost = 370 * 0.5
    carrot_cost = 185

    cookie_cost = 370 * 0.2
    cookie_cost = 74

    total_cost = burger_cost + carrot_cost + cookie_cost
    total_cost = burger_cost + carrot_cost + cookie_cost = (370 * x) + (185) + (74) = 370 * x + 185 + 74
    total_cost = burger_cost + carrot_cost + cookie_cost = (370 * x) + (185) + (74) = 370 * x + 259

    370 * x + 259 = 1036
    370 * x = 1036 - 259
    370 * x = 777

    x = 777 / 370
    x = 2.1
```

## 7. `MetaMathQA-GSM_Rephrased-284715`

```yaml
id: "MetaMathQA-GSM_Rephrased-284715"
source: "MetaMathQA"
topic: "augmented arithmetic and algebra QA"
difficulty: "mixed"
natural_language_idea: "Use the generated QA solution as a Litex arithmetic or algebra derivation with explicit intermediate quantities."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
claim:
    prove:
        forall num_warehouse_workers, num_managers, wage_warehouse, wage_manager, days, hours_per_day, fica_rate, warehouse_daily, manager_daily, total_daily, monthly_wages, fica, total R:
            num_warehouse_workers = 4
            num_managers = 2
            wage_warehouse = 15
            wage_manager = 20
            days = 25
            hours_per_day = 8
            fica_rate = 0.10
            warehouse_daily = num_warehouse_workers * wage_warehouse * hours_per_day
            manager_daily = num_managers * wage_manager * hours_per_day
            total_daily = warehouse_daily + manager_daily
            monthly_wages = total_daily * days
            fica = monthly_wages * fica_rate
            total = monthly_wages + fica
            =>:
                total = 22000
    warehouse_daily = 4 * 15 * 8
    warehouse_daily = 480

    manager_daily = 2 * 20 * 8
    manager_daily = 320

    total_daily = warehouse_daily + manager_daily = (480) + (320) = 480 + 320
    total_daily = warehouse_daily + manager_daily = (480) + (320) = 800

    monthly_wages = 800 * 25
    monthly_wages = 20000

    fica = 20000 * 0.10
    fica = 2000

    total = monthly_wages + fica = (20000) + (2000) = 20000 + 2000
    total = monthly_wages + fica = (20000) + (2000) = 22000
```

## 8. `MetaMathQA-GSM_Rephrased-330032`

```yaml
id: "MetaMathQA-GSM_Rephrased-330032"
source: "MetaMathQA"
topic: "augmented arithmetic and algebra QA"
difficulty: "mixed"
natural_language_idea: "Use the generated QA solution as a Litex arithmetic or algebra derivation with explicit intermediate quantities."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
claim:
    prove:
        forall dress_shirts, pants, suit, sweaters, total_before_discount, twenty_percent_discount, total_after_twenty_percent, ten_percent_coupon, final_total R:
            dress_shirts = 4 * 15
            pants = 2 * 40
            suit = 150
            sweaters = 2 * 30
            total_before_discount = dress_shirts + pants + suit + sweaters
            twenty_percent_discount = 0.2 * total_before_discount
            total_after_twenty_percent = total_before_discount - twenty_percent_discount
            ten_percent_coupon = 0.1 * total_after_twenty_percent
            final_total = total_after_twenty_percent - ten_percent_coupon
            =>:
                final_total = 252
    dress_shirts = 4 * 15
    dress_shirts = 60

    pants = 2 * 40
    pants = 80

    suit = 150

    sweaters = 2 * 30
    sweaters = 60

    total_before_discount = dress_shirts + pants + suit + sweaters = (60) + (80) + (150) + (60) = 60 + 80 + 150 + 60
    total_before_discount = dress_shirts + pants + suit + sweaters = (60) + (80) + (150) + (60) = 350

    twenty_percent_discount = 0.2 * total_before_discount = 0.2 * (350) = 0.2 * 350
    twenty_percent_discount = 0.2 * total_before_discount = 0.2 * (350) = 70

    total_after_twenty_percent = total_before_discount - twenty_percent_discount = (350) - (70) = 350 - 70
    total_after_twenty_percent = total_before_discount - twenty_percent_discount = (350) - (70) = 280

    ten_percent_coupon = 0.1 * total_after_twenty_percent = 0.1 * (280) = 0.1 * 280
    ten_percent_coupon = 0.1 * total_after_twenty_percent = 0.1 * (280) = 28

    final_total = total_after_twenty_percent - ten_percent_coupon = (280) - (28) = 280 - 28
    final_total = total_after_twenty_percent - ten_percent_coupon = (280) - (28) = 252
```

## 9. `MetaMathQA-GSM_Rephrased-331024`

```yaml
id: "MetaMathQA-GSM_Rephrased-331024"
source: "MetaMathQA"
topic: "augmented arithmetic and algebra QA"
difficulty: "mixed"
natural_language_idea: "Use the generated QA solution as a Litex arithmetic or algebra derivation with explicit intermediate quantities."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
claim:
    prove:
        forall tulip_price, rose_price, d1_tulips, d1_roses, d1_tulip_rev, d1_rose_rev, d1_total, d2_tulips, d2_roses, d2_tulip_rev, d2_rose_rev, d2_total, d3_tulips, d3_roses, d3_tulip_rev, d3_rose_rev, d3_total, total R:
            tulip_price = 2
            rose_price   = 3

            d1_tulips = 30
            d1_roses  = 20
            d1_tulip_rev = d1_tulips * tulip_price
            d1_rose_rev  = d1_roses  * rose_price
            d1_total = d1_tulip_rev + d1_rose_rev

            d2_tulips = d1_tulips * 2
            d2_roses  = d1_roses  * 2
            d2_tulip_rev = tulip_price * d2_tulips
            d2_rose_rev  = rose_price  * d2_roses
            d2_total = d2_tulip_rev + d2_rose_rev

            d3_tulips = d2_tulips * (1/10)
            d3_roses  = 16
            d3_tulip_rev = tulip_price * d3_tulips
            d3_rose_rev  = rose_price  * d3_roses
            d3_total = d3_tulip_rev + d3_rose_rev

            total = d1_total + d2_total + d3_total
            =>:
                total = 420
    d1_tulip_rev = 30 * 2
    d1_tulip_rev = 60

    d1_rose_rev = 20 * 3
    d1_rose_rev = 60

    d1_total = d1_tulip_rev + d1_rose_rev = (60) + (60) = 60 + 60
    d1_total = d1_tulip_rev + d1_rose_rev = (60) + (60) = 120

    d2_tulips = 30 * 2
    d2_tulips = 60

    d2_roses = 20 * 2
    d2_roses = 40

    d2_tulip_rev = 2 * 60
    d2_tulip_rev = 120

    d2_rose_rev = 3 * 40
    d2_rose_rev = 120

    d2_total = d2_tulip_rev + d2_rose_rev = (120) + (120) = 120 + 120
    d2_total = d2_tulip_rev + d2_rose_rev = (120) + (120) = 240

    d3_tulips = d2_tulips * (1/10) = (60) * (1/10) = 60 * (1/10)
    d3_tulips = d2_tulips * (1/10) = (60) * (1/10) = 6

    d3_rose_rev = 3 * 16
    d3_rose_rev = 48

    d3_tulip_rev = 2 * 6
    d3_tulip_rev = 12

    d3_total = d3_tulip_rev + d3_rose_rev = (12) + (48) = 12 + 48
    d3_total = d3_tulip_rev + d3_rose_rev = (12) + (48) = 60

    total = d1_total + d2_total + d3_total = (120) + (240) + (60) = 120 + 240 + 60
    total = d1_total + d2_total + d3_total = (120) + (240) + (60) = 420
```

## 10. `MetaMathQA-GSM_Rephrased-332285`

```yaml
id: "MetaMathQA-GSM_Rephrased-332285"
source: "MetaMathQA"
topic: "augmented arithmetic and algebra QA"
difficulty: "mixed"
natural_language_idea: "Use the generated QA solution as a Litex arithmetic or algebra derivation with explicit intermediate quantities."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
claim:
    prove:
        forall soup_qty, soup_price, soup_cost, bread_qty, bread_price, bread_cost, cereal_qty, cereal_price, cereal_cost, milk_qty, milk_price, milk_cost, total_cost, bill_value, bills_fraction, bills_needed R:
            soup_qty = 6
            soup_price = 2
            soup_cost = soup_qty * soup_price

            bread_qty = 2
            bread_price = 5
            bread_cost = bread_qty * bread_price

            cereal_qty = 2
            cereal_price = 3
            cereal_cost = cereal_qty * cereal_price

            milk_qty = 2
            milk_price = 4
            milk_cost = milk_qty * milk_price

            total_cost = soup_cost + bread_cost + cereal_cost + milk_cost
            bill_value = 10

            bills_fraction = total_cost / bill_value
            bills_needed = 4
            =>:
                bills_needed = 4
    soup_cost = 6 * 2
    soup_cost = 12

    bread_cost = 2 * 5
    bread_cost = 10

    cereal_cost = 2 * 3
    cereal_cost = 6

    milk_cost = 2 * 4
    milk_cost = 8

    total_cost = soup_cost + bread_cost + cereal_cost + milk_cost = (12) + (10) + (6) + (8) = 12 + 10 + 6 + 8
    total_cost = soup_cost + bread_cost + cereal_cost + milk_cost = (12) + (10) + (6) + (8) = 36

    bills_fraction = 36 / 10
    bills_fraction = 3.6

    3 * 10 = 30
    30 < 36

    4 * 10 = 40
    40 >= 36

    bills_needed = 4
```

## 11. `MetaMathQA-GSM_Rephrased-350263`

```yaml
id: "MetaMathQA-GSM_Rephrased-350263"
source: "MetaMathQA"
topic: "augmented arithmetic and algebra QA"
difficulty: "mixed"
natural_language_idea: "Use the generated QA solution as a Litex arithmetic or algebra derivation with explicit intermediate quantities."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
claim:
    prove:
        forall budget, math_books, math_cost_each, math_spent, science_more_than_math, science_books, science_cost_each, science_spent, art_multiplier, art_books, art_cost_each, art_spent, subtotal_spent, music_spent N_pos:
            budget = 500
            math_books = 4
            math_cost_each = 20
            science_more_than_math = 6
            science_cost_each = 10
            art_multiplier = 2
            art_cost_each = 20
            math_spent = math_books * math_cost_each
            science_books = math_books + science_more_than_math
            science_spent = science_books * science_cost_each
            art_books = math_books * art_multiplier
            art_spent = art_books * art_cost_each
            subtotal_spent = math_spent + science_spent + art_spent
            music_spent = budget - subtotal_spent
            =>:
                music_spent = 160
    math_spent = math_books * math_cost_each = math_books * math_cost_each
    math_spent = 4 * 20
    math_spent = 80

    science_books = math_books + science_more_than_math = math_books + science_more_than_math
    science_books = 4 + 6
    science_books = 10
    science_spent = science_books * science_cost_each
    science_spent = 10 * 10
    science_spent = 100

    art_books = math_books * art_multiplier = math_books * art_multiplier
    art_books = 4 * 2
    art_books = 8
    art_spent = art_books * art_cost_each
    art_spent = 8 * 20
    art_spent = 160

    subtotal_spent = math_spent + science_spent + art_spent
    subtotal_spent = math_spent + science_spent + art_spent = (80) + (100) + (160) = 80 + 100 + 160
    subtotal_spent = math_spent + science_spent + art_spent = (80) + (100) + (160) = 340

    music_spent = budget - subtotal_spent
    music_spent = 500 - 340
    music_spent = 160
```

## 12. `MetaMathQA-GSM_Rephrased-358548`

```yaml
id: "MetaMathQA-GSM_Rephrased-358548"
source: "MetaMathQA"
topic: "augmented arithmetic and algebra QA"
difficulty: "mixed"
natural_language_idea: "Use the generated QA solution as a Litex arithmetic or algebra derivation with explicit intermediate quantities."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
claim:
    prove:
        forall dimes_initial, quarters_initial, cents_per_dime, cents_per_quarter, cents_from_dimes, cents_from_quarters, candy_bars, dimes_per_candy_bar, total_dimes_for_candy, cents_spent_on_candy, quarters_for_lollipop, cents_spent_on_lollipop, total_spent, initial_cents_total, remaining_cents N_pos:
            dimes_initial = 19
            quarters_initial = 6
            cents_per_dime = 10
            cents_per_quarter = 25
            cents_from_dimes = dimes_initial * cents_per_dime
            cents_from_quarters = quarters_initial * cents_per_quarter
            candy_bars = 4
            dimes_per_candy_bar = 3
            total_dimes_for_candy = candy_bars * dimes_per_candy_bar
            cents_spent_on_candy = total_dimes_for_candy * cents_per_dime
            quarters_for_lollipop = 1
            cents_spent_on_lollipop = quarters_for_lollipop * cents_per_quarter
            total_spent = cents_spent_on_candy + cents_spent_on_lollipop
            initial_cents_total = cents_from_dimes + cents_from_quarters
            remaining_cents = initial_cents_total - total_spent
            =>:
                remaining_cents = 195
    cents_from_dimes = 19 * 10
    cents_from_dimes = 190

    cents_from_quarters = 6 * 25
    cents_from_quarters = 150

    total_dimes_for_candy = 4 * 3
    total_dimes_for_candy = 12

    cents_spent_on_candy = 12 * 10
    cents_spent_on_candy = 120

    cents_spent_on_lollipop = 1 * 25
    cents_spent_on_lollipop = 25

    total_spent = cents_spent_on_candy + cents_spent_on_lollipop = (120) + (25) = 120 + 25
    total_spent = cents_spent_on_candy + cents_spent_on_lollipop = (120) + (25) = 145

    initial_cents_total = cents_from_dimes + cents_from_quarters = (190) + (150) = 190 + 150
    initial_cents_total = cents_from_dimes + cents_from_quarters = (190) + (150) = 340

    remaining_cents = initial_cents_total - total_spent = (340) - (145) = 340 - 145
    remaining_cents = initial_cents_total - total_spent = (340) - (145) = 195
```

## 13. `MetaMathQA-GSM_Rephrased-359152`

```yaml
id: "MetaMathQA-GSM_Rephrased-359152"
source: "MetaMathQA"
topic: "augmented arithmetic and algebra QA"
difficulty: "mixed"
natural_language_idea: "Use the generated QA solution as a Litex arithmetic or algebra derivation with explicit intermediate quantities."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
claim:
    prove:
        forall pairs, shoes_unit_price, shoes_original_total, shoes_discount_percent, shoes_discount_fraction, shoes_discount_amount, shoes_final, dress_price, dress_discount_percent, dress_discount_fraction, dress_discount_amount, dress_final, total R:
            pairs = 2
            shoes_unit_price = 50
            shoes_original_total = pairs * shoes_unit_price
            shoes_discount_percent = 40
            shoes_discount_fraction = shoes_discount_percent / 100
            shoes_discount_amount = shoes_discount_fraction * shoes_original_total
            shoes_final = shoes_original_total - shoes_discount_amount
            dress_price = 100
            dress_discount_percent = 20
            dress_discount_fraction = dress_discount_percent / 100
            dress_discount_amount = dress_discount_fraction * dress_price
            dress_final = dress_price - dress_discount_amount
            total = shoes_final + dress_final
            =>:
                total = 140
    shoes_original_total = 2 * 50
    shoes_original_total = 100

    shoes_discount_fraction = 40 / 100
    shoes_discount_amount = shoes_discount_fraction * shoes_original_total = (40 / 100) * (100) = (40 / 100) * 100
    shoes_discount_amount = shoes_discount_fraction * shoes_original_total = (40 / 100) * (100) = 40

    shoes_final = shoes_original_total - shoes_discount_amount = (100) - (40) = 100 - 40
    shoes_final = shoes_original_total - shoes_discount_amount = (100) - (40) = 60

    dress_discount_fraction = 20 / 100
    dress_discount_amount = (20 / 100) * 100
    dress_discount_amount = 20

    dress_final = 100 - 20
    dress_final = 80

    total = shoes_final + dress_final = (60) + (80) = 60 + 80
    total = shoes_final + dress_final = (60) + (80) = 140
```

## 14. `MetaMathQA-MATH_AnsAug-160056`

```yaml
id: "MetaMathQA-MATH_AnsAug-160056"
source: "MetaMathQA"
topic: "augmented arithmetic and algebra QA"
difficulty: "mixed"
natural_language_idea: "Use the generated QA solution as a Litex arithmetic or algebra derivation with explicit intermediate quantities."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
claim:
    prove:
        forall a, b, c, d, e, f, numerator_real, numerator_imag, denominator_real, result_real, result_imag R:
            a = 5
            b = 12
            c = 2
            d = -3
            e = c
            f = -d
            numerator_real = a * e - b * f
            numerator_imag = a * f + b * e
            denominator_real = c * e - d * f
            result_real = numerator_real / denominator_real
            result_imag = numerator_imag / denominator_real
            =>:
                result_real = -2
                result_imag = 3
    e = c = c
    e = 2

    f = -d = -d
    d = -3
    f = -d = -(-3)
    f = -d = -(-3) = 3

    numerator_real = 5 * 2 - 12 * 3
    numerator_real = 10 - 36
    numerator_real = -26

    numerator_imag = 5 * 3 + 12 * 2
    numerator_imag = 15 + 24
    numerator_imag = 39

    denominator_real = 2 * 2 - (-3) * 3
    denominator_real = 4 + 9
    denominator_real = 13

    result_real = numerator_real / denominator_real = (-26) / (13) = -26 / 13
    result_real = numerator_real / denominator_real = (-26) / (13) = -2

    result_imag = numerator_imag / denominator_real = (39) / (13) = 39 / 13
    result_imag = numerator_imag / denominator_real = (39) / (13) = 3
```

## 15. `MetaMathQA-MATH_AnsAug-162388`

```yaml
id: "MetaMathQA-MATH_AnsAug-162388"
source: "MetaMathQA"
topic: "augmented arithmetic and algebra QA"
difficulty: "mixed"
natural_language_idea: "Use the generated QA solution as a Litex arithmetic or algebra derivation with explicit intermediate quantities."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
prop difference_of_squares(a, b R):
    a^2 - b^2 = (a + b) * (a - b)

claim:
    prove:
        forall total R:
            total = 19^2 - 17^2 + 15^2 - 13^2 + 11^2 - 9^2 + 7^2 - 5^2 + 3^2 - 1^2
            =>:
                total = 200
    $difference_of_squares(19, 17)
    19^2 - 17^2 = (19 + 17) * (19 - 17)
    19 + 17 = 36
    19 - 17 = 2
    (19 + 17) * (19 - 17) = 36 * 2
    36 * 2 = 72
    19^2 - 17^2 = 72

    $difference_of_squares(15, 13)
    15^2 - 13^2 = (15 + 13) * (15 - 13)
    15 + 13 = 28
    15 - 13 = 2
    (15 + 13) * (15 - 13) = 28 * 2
    28 * 2 = 56
    15^2 - 13^2 = 56

    $difference_of_squares(11, 9)
    11^2 - 9^2 = (11 + 9) * (11 - 9)
    11 + 9 = 20
    11 - 9 = 2
    (11 + 9) * (11 - 9) = 20 * 2
    20 * 2 = 40
    11^2 - 9^2 = 40

    $difference_of_squares(7, 5)
    7^2 - 5^2 = (7 + 5) * (7 - 5)
    7 + 5 = 12
    7 - 5 = 2
    (7 + 5) * (7 - 5) = 12 * 2
    12 * 2 = 24
    7^2 - 5^2 = 24

    $difference_of_squares(3, 1)
    3^2 - 1^2 = (3 + 1) * (3 - 1)
    3 + 1 = 4
    3 - 1 = 2
    (3 + 1) * (3 - 1) = 4 * 2
    4 * 2 = 8
    3^2 - 1^2 = 8

    total = 72 + 56 + 40 + 24 + 8
    72 + 56 = 128
    128 + 40 = 168
    168 + 24 = 192
    192 + 8 = 200
    total = 200
```

## 16. `MetaMathQA-MATH_AnsAug-332284`

```yaml
id: "MetaMathQA-MATH_AnsAug-332284"
source: "MetaMathQA"
topic: "augmented arithmetic and algebra QA"
difficulty: "mixed"
natural_language_idea: "Use the generated QA solution as a Litex arithmetic or algebra derivation with explicit intermediate quantities."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
claim:
    prove:
        forall area, side, half, cx, cy, v1x, v1y, v2x, v2y, v3x, v3y, v4x, v4y, s, u1x, u1y, u2x, u2y, u3x, u3y, u4x, u4y, d1, d2, d3, d4, ansx, ansy R:
            area = 4
            side = 2
            half = side / 2
            cx = 8
            cy = -8

            v1x = cx - half
            v1y = cy + half
            v2x = cx + half
            v2y = cy + half
            v3x = cx - half
            v3y = cy - half
            v4x = cx + half
            v4y = cy - half

            s = 2
            u1x = s * v1x
            u1y = s * v1y
            u2x = s * v2x
            u2y = s * v2y
            u3x = s * v3x
            u3y = s * v3y
            u4x = s * v4x
            u4y = s * v4y

            d1 = u1x ^ 2 + u1y ^ 2
            d2 = u2x ^ 2 + u2y ^ 2
            d3 = u3x ^ 2 + u3y ^ 2
            d4 = u4x ^ 2 + u4y ^ 2

            ansx = u4x
            ansy = u4y
            =>:
                ansx = 18
                ansy = -18
    half = 2 / 2
    half = 1

    v1x = 8 - 1
    v1x = 7
    v1y = -8 + 1
    v1y = -7

    v2x = 8 + 1
    v2x = 9
    v2y = -8 + 1
    v2y = -7

    v3x = 8 - 1
    v3x = 7
    v3y = -8 - 1
    v3y = -9

    v4x = 8 + 1
    v4x = 9
    v4y = -8 - 1
    v4y = -9

    u1x = 2 * 7
    u1x = 14
    u1y = 2 * (-7)
    u1y = -14

    u2x = 2 * 9
    u2x = 18
    u2y = 2 * (-7)
    u2y = -14

    u3x = 2 * 7
    u3x = 14
    u3y = 2 * (-9)
    u3y = -18

    u4x = 2 * 9
    u4x = 18
    u4y = 2 * (-9)
    u4y = -18

    d1 = u1x ^ 2 + u1y ^ 2
    d1 = u1x ^ 2 + u1y ^ 2 = (14) ^ 2 + (-14) ^ 2 = 14 ^ 2 + (-14) ^ 2
    d1 = u1x ^ 2 + u1y ^ 2 = (14) ^ 2 + (-14) ^ 2 = 196 + 196
    d1 = u1x ^ 2 + u1y ^ 2 = (14) ^ 2 + (-14) ^ 2 = 392

    d2 = u2x ^ 2 + u2y ^ 2
    d2 = u2x ^ 2 + u2y ^ 2 = (18) ^ 2 + (-14) ^ 2 = 18 ^ 2 + (-14) ^ 2
    d2 = u2x ^ 2 + u2y ^ 2 = (18) ^ 2 + (-14) ^ 2 = 324 + 196
    d2 = u2x ^ 2 + u2y ^ 2 = (18) ^ 2 + (-14) ^ 2 = 520

    d3 = u3x ^ 2 + u3y ^ 2
    d3 = u3x ^ 2 + u3y ^ 2 = (14) ^ 2 + (-18) ^ 2 = 14 ^ 2 + (-18) ^ 2
    d3 = u3x ^ 2 + u3y ^ 2 = (14) ^ 2 + (-18) ^ 2 = 196 + 324
    d3 = u3x ^ 2 + u3y ^ 2 = (14) ^ 2 + (-18) ^ 2 = 520

    d4 = u4x ^ 2 + u4y ^ 2
    d4 = u4x ^ 2 + u4y ^ 2 = (18) ^ 2 + (-18) ^ 2 = 18 ^ 2 + (-18) ^ 2
    d4 = u4x ^ 2 + u4y ^ 2 = (18) ^ 2 + (-18) ^ 2 = 324 + 324
    d4 = u4x ^ 2 + u4y ^ 2 = (18) ^ 2 + (-18) ^ 2 = 648

    ansx = u4x
    ansx = u4x = (18) = 18
    ansy = u4y
    ansy = u4y = (-18) = -18
```

## 17. `MetaMathQA-MATH_AnsAug-332536`

```yaml
id: "MetaMathQA-MATH_AnsAug-332536"
source: "MetaMathQA"
topic: "augmented arithmetic and algebra QA"
difficulty: "mixed"
natural_language_idea: "Use the generated QA solution as a Litex arithmetic or algebra derivation with explicit intermediate quantities."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
claim:
    prove:
        forall total_digits, total_letters, total_passwords, odd_digits, positive_digits, favorable, probability R:
            total_digits = 10
            total_letters = 26
            total_passwords = total_digits * total_letters * total_digits
            odd_digits = 5
            positive_digits = 9
            favorable = odd_digits * total_letters * positive_digits
            probability = favorable / total_passwords
            =>:
                probability = 9/20
    total_passwords = 10 * 26 * 10
    total_passwords = (10 * 26) * 10
    total_passwords = 260 * 10
    total_passwords = 2600

    favorable = 5 * 26 * 9
    favorable = (5 * 26) * 9
    favorable = 130 * 9
    favorable = 1170

    probability = favorable / total_passwords
    probability = favorable / total_passwords = (1170) / (2600) = 1170 / 2600

    1170 = 117 * 10
    2600 = 260 * 10
    probability = favorable / total_passwords = (1170) / (2600) = (117 * 10) / (260 * 10)
    probability = favorable / total_passwords = (1170) / (2600) = 117 / 260

    117 = 9 * 13
    260 = 20 * 13
    probability = favorable / total_passwords = (1170) / (2600) = (9 * 13) / (20 * 13)
    probability = favorable / total_passwords = (1170) / (2600) = 9 / 20
```

## 18. `MetaMathQA-MATH_AnsAug-382281`

```yaml
id: "MetaMathQA-MATH_AnsAug-382281"
source: "MetaMathQA"
topic: "augmented arithmetic and algebra QA"
difficulty: "mixed"
natural_language_idea: "Use the generated QA solution as a Litex arithmetic or algebra derivation with explicit intermediate quantities."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
claim:
    prove:
        forall original_price, discount1_percent, discount2_percent, first_discount_amount, sale_price, second_discount_amount, final_price, single_discount_percent N_pos:
            original_price = 30
            discount1_percent = 20
            discount2_percent = 25
            first_discount_amount = original_price * (discount1_percent / 100)
            sale_price = original_price - first_discount_amount
            second_discount_amount = sale_price * (discount2_percent / 100)
            final_price = sale_price - second_discount_amount
            single_discount_percent = 100 - (final_price / original_price) * 100
            =>:
                single_discount_percent = 40
    first_discount_amount = 30 * (20 / 100)
    first_discount_amount = 30 * 0.2
    first_discount_amount = 6

    sale_price = 30 - 6
    sale_price = 24

    second_discount_amount = 24 * (25 / 100)
    second_discount_amount = 24 * 0.25
    second_discount_amount = 6

    final_price = sale_price - second_discount_amount = (24) - (6) = 24 - 6
    final_price = sale_price - second_discount_amount = (24) - (6) = 18

    single_discount_percent = 100 - (18 / 30) * 100
    single_discount_percent = 100 - 60
    single_discount_percent = 40
```

## 19. `MetaMathQA-MATH_Rephrased-332312`

```yaml
id: "MetaMathQA-MATH_Rephrased-332312"
source: "MetaMathQA"
topic: "augmented arithmetic and algebra QA"
difficulty: "mixed"
natural_language_idea: "Use the generated QA solution as a Litex arithmetic or algebra derivation with explicit intermediate quantities."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
claim:
    prove:
        forall b, d4, d3, d2, d1, d0, t4, t3, t2, t1, t0, s R:
            b = 3
            d4 = 1
            d3 = 0
            d2 = 1
            d1 = 0
            d0 = 1
            t4 = d4 * (b ^ 4)
            t3 = d3 * (b ^ 3)
            t2 = d2 * (b ^ 2)
            t1 = d1 * (b ^ 1)
            t0 = d0 * (b ^ 0)
            s = t4 + t3 + t2 + t1 + t0
            =>:
                s = 91
    t4 = 1 * (3 ^ 4)
    3 ^ 4 = 81
    t4 = 1 * 81
    t4 = 81

    t3 = 0 * (3 ^ 3)
    3 ^ 3 = 27
    t3 = 0 * 27
    t3 = 0

    t2 = 1 * (3 ^ 2)
    3 ^ 2 = 9
    t2 = 1 * 9
    t2 = 9

    t1 = 0 * (3 ^ 1)
    3 ^ 1 = 3
    t1 = 0 * 3
    t1 = 0

    t0 = 1 * (3 ^ 0)
    3 ^ 0 = 1
    t0 = 1 * 1
    t0 = 1

    s = t4 + t3 + t2 + t1 + t0
    s = 81 + t3 + t2 + t1 + t0
    s = 81 + 0 + t2 + t1 + t0
    s = 81 + 0 + 9 + t1 + t0
    s = 81 + 0 + 9 + 0 + t0
    s = t4 + t3 + t2 + t1 + t0 = (81) + (0) + (9) + (0) + (1) = 81 + 0 + 9 + 0 + 1
    s = t4 + t3 + t2 + t1 + t0 = (81) + (0) + (9) + (0) + (1) = 81 + 0 + 9 + 1
    s = t4 + t3 + t2 + t1 + t0 = (81) + (0) + (9) + (0) + (1) = 81 + 9 + 1
    s = t4 + t3 + t2 + t1 + t0 = (81) + (0) + (9) + (0) + (1) = 81 + 10
    s = t4 + t3 + t2 + t1 + t0 = (81) + (0) + (9) + (0) + (1) = 91
```

## 20. `MetaMathQA-MATH_SV-332270`

```yaml
id: "MetaMathQA-MATH_SV-332270"
source: "MetaMathQA"
topic: "augmented arithmetic and algebra QA"
difficulty: "mixed"
natural_language_idea: "Use the generated QA solution as a Litex arithmetic or algebra derivation with explicit intermediate quantities."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
claim:
    prove:
        forall x, n3, n4, n5, n6, n7, n8, n9, a4, a5, a6, a7, a8, a9, t4, t5, t6, t7, t8, t9, t10 N:
            x = 10
            n3 = 0
            n4 = 1
            n5 = 2
            n6 = 4
            n7 = 6
            n8 = 9
            n9 = 12
            a4 = n3 + n4
            a5 = a4 + n5
            a6 = a5 + n6
            a7 = a6 + n7
            a8 = a7 + n8
            a9 = a8 + n9
            t4 = 0
            t5 = t4 + a4
            t6 = t5 + a5
            t7 = t6 + a6
            t8 = t7 + a7
            t9 = t8 + a8
            t10 = t9 + a9
            =>:
                x = 10
                t10 = 80
    a4 = 0 + 1
    a4 = 1

    a5 = 1 + 2
    a5 = 3

    a6 = 3 + 4
    a6 = 7

    a7 = 7 + 6
    a7 = 13

    a8 = 13 + 9
    a8 = 22

    a9 = 22 + 12
    a9 = 34

    t5 = 0 + 1
    t5 = 1

    t6 = t5 + a5 = (1) + (3) = 1 + 3
    t6 = t5 + a5 = (1) + (3) = 4

    t7 = t6 + a6 = (4) + (7) = 4 + 7
    t7 = t6 + a6 = (4) + (7) = 11

    t8 = t7 + a7 = (11) + (13) = 11 + 13
    t8 = t7 + a7 = (11) + (13) = 24

    t9 = t8 + a8 = (24) + (22) = 24 + 22
    t9 = t8 + a8 = (24) + (22) = 46

    t10 = t9 + a9 = (46) + (34) = 46 + 34
    t10 = t9 + a9 = (46) + (34) = 80
```
