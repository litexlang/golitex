# GSM8K

Arithmetic word-problem derivations that name quantities and verify the calculation chain.

Each example below is an independent checked Litex snippet. The metadata record keeps the dataset translation fields next to the runnable code.

## 1. `gsm8k_1103`

```yaml
id: "gsm8k_1103"
source: "GSM8K"
topic: "grade-school arithmetic word problem"
difficulty: "test"
natural_language_idea: "Name the quantities in the word problem, encode the arithmetic relationships, and check the final numerical result."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
claim:
    prove:
        forall initial_charge, returned_amount, balance_after_return, frying_pan_price, frying_pan_discount_rate, frying_pan_discount_amount, frying_pan_final_price, towel_price, towel_discount_rate, towel_discount_amount, towel_final_price, new_purchases_total, new_balance R:
            initial_charge = 85.00
            returned_amount = 15.00
            balance_after_return = initial_charge - returned_amount
            frying_pan_price = 20.00
            frying_pan_discount_rate = 0.20
            frying_pan_discount_amount = frying_pan_discount_rate * frying_pan_price
            frying_pan_final_price = frying_pan_price - frying_pan_discount_amount
            towel_price = 30.00
            towel_discount_rate = 0.10
            towel_discount_amount = towel_discount_rate * towel_price
            towel_final_price = towel_price - towel_discount_amount
            new_purchases_total = frying_pan_final_price + towel_final_price
            new_balance = balance_after_return + new_purchases_total
            =>:
                initial_charge = 85.00 
        returned_amount = 15.00 
        balance_after_return = initial_charge - returned_amount 
        frying_pan_price = 20.00 
        frying_pan_discount_rate = 0.20 
        frying_pan_discount_amount = frying_pan_discount_rate * frying_pan_price 
        frying_pan_final_price = frying_pan_price - frying_pan_discount_amount 
        towel_price = 30.00 
        towel_discount_rate = 0.10 
        towel_discount_amount = towel_discount_rate * towel_price 
        towel_final_price = towel_price - towel_discount_amount 
        new_purchases_total = frying_pan_final_price + towel_final_price 
        new_balance = balance_after_return + new_purchases_total 
        new_balance = 113.00
    balance_after_return = 85.00 - 15.00 = 70.00
        
    frying_pan_discount_amount = 0.20 * 20.00 = 4.00
    frying_pan_final_price = 20.00 - 4.00 = 16.00
        
    towel_discount_amount = 0.10 * 30.00 = 3.00
    towel_final_price = 30.00 - 3.00 = 27.00
        
    new_purchases_total = 16.00 + 27.00 = 43.00
        
    new_balance = 70.00 + 43.00 = 113.00
```

## 2. `gsm8k_1186`

```yaml
id: "gsm8k_1186"
source: "GSM8K"
topic: "grade-school arithmetic word problem"
difficulty: "test"
natural_language_idea: "Name the quantities in the word problem, encode the arithmetic relationships, and check the final numerical result."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
claim:
    prove:
        forall cheese_slices_per_pie, pepperoni_slices_per_pie, friends_count, cheese_slices_per_friend, pepperoni_slices_per_friend, total_cheese_slices, total_pepperoni_slices, cheese_pies, pepperoni_pies, total_pies R:
            cheese_slices_per_pie = 12
            pepperoni_slices_per_pie = 8
            friends_count = 6
            cheese_slices_per_friend = 6
            pepperoni_slices_per_friend = 4
            total_cheese_slices = friends_count * cheese_slices_per_friend
            total_pepperoni_slices = friends_count * pepperoni_slices_per_friend
            cheese_pies = total_cheese_slices / cheese_slices_per_pie
            pepperoni_pies = total_pepperoni_slices / pepperoni_slices_per_pie
            total_pies = cheese_pies + pepperoni_pies
            =>:
                cheese_slices_per_pie = 12 
        pepperoni_slices_per_pie = 8 
        friends_count = 6 
        cheese_slices_per_friend = 6 
        pepperoni_slices_per_friend = 4 
        total_cheese_slices = friends_count * cheese_slices_per_friend 
        total_pepperoni_slices = friends_count * pepperoni_slices_per_friend 
        cheese_pies = total_cheese_slices / cheese_slices_per_pie 
        pepperoni_pies = total_pepperoni_slices / pepperoni_slices_per_pie 
        total_pies = cheese_pies + pepperoni_pies 
        total_pies = 6
    total_cheese_slices = 6 * 6 = 36
        
    total_pepperoni_slices = 6 * 4 = 24
        
    cheese_pies = 36 / 12 = 3
        
    pepperoni_pies = 24 / 8 = 3
        
    total_pies = 3 + 3 = 6
```

## 3. `gsm8k_13`

```yaml
id: "gsm8k_13"
source: "GSM8K"
topic: "grade-school arithmetic word problem"
difficulty: "test"
natural_language_idea: "Name the quantities in the word problem, encode the arithmetic relationships, and check the final numerical result."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
claim:
    prove:
        forall tree_cost, lemons_per_year, lemon_price, water_cost_per_year, income_per_year, year_to_make_profit R:
            tree_cost = 90
            lemons_per_year = 7
            lemon_price = 1.5
            water_cost_per_year = 3
            income_per_year = lemon_price * lemons_per_year - water_cost_per_year
            year_to_make_profit = tree_cost / income_per_year + 1 
            =>:
                tree_cost = 90 
        lemons_per_year = 7 
        lemon_price = 1.5 
        water_cost_per_year = 3 
        income_per_year = lemon_price * lemons_per_year - water_cost_per_year 
        year_to_make_profit = tree_cost / income_per_year + 1 
        year_to_make_profit = 13
    income_per_year = 1.5 * 7 - 3 = 10.5 - 3 = 7.5

    year_to_make_profit = 90 / 7.5 + 1 = 12 + 1 = 13
```

## 4. `gsm8k_1315`

```yaml
id: "gsm8k_1315"
source: "GSM8K"
topic: "grade-school arithmetic word problem"
difficulty: "test"
natural_language_idea: "Name the quantities in the word problem, encode the arithmetic relationships, and check the final numerical result."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
claim:
    prove:
        forall dora_future_age, years_until_doras_birthday, dora_current_age, james_current_age, johns_age_at_james_birth, john_current_age, johns_age_at_youngest_birth, youngest_current_age, youngest_age_in_3_years N_pos:
            dora_future_age = 12
            years_until_doras_birthday = 3
            dora_current_age = dora_future_age - years_until_doras_birthday
            james_current_age = 2 * dora_current_age
            johns_age_at_james_birth = 19
            john_current_age = james_current_age + johns_age_at_james_birth
            johns_age_at_youngest_birth = 32
            youngest_current_age = john_current_age - johns_age_at_youngest_birth
            youngest_age_in_3_years = youngest_current_age + years_until_doras_birthday
            =>:
                dora_future_age = 12 
        years_until_doras_birthday = 3 
        dora_current_age = dora_future_age - years_until_doras_birthday 
        james_current_age = 2 * dora_current_age 
        johns_age_at_james_birth = 19 
        john_current_age = james_current_age + johns_age_at_james_birth 
        johns_age_at_youngest_birth = 32 
        youngest_current_age = john_current_age - johns_age_at_youngest_birth 
        youngest_age_in_3_years = youngest_current_age + years_until_doras_birthday 
        youngest_age_in_3_years = 8
    dora_current_age = 12 - 3 = 9
        
    james_current_age = 2 * 9 = 18
        
    john_current_age = 18 + 19 = 37
        
    youngest_current_age = 37 - 32 = 5
        
    youngest_age_in_3_years = 5 + 3 = 8
```

## 5. `gsm8k_14`

```yaml
id: "gsm8k_14"
source: "GSM8K"
topic: "grade-school arithmetic word problem"
difficulty: "test"
natural_language_idea: "Name the quantities in the word problem, encode the arithmetic relationships, and check the final numerical result."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
claim:
    prove:
        forall x R:
            2 != 0
            (x * (1 - 1 / 3) - 2) / 2 = 5
            x * (1 - 1 / 3) - 2 = 10
            x * (1 - 1 / 3) = 12
            x = 18
            =>:
                2 != 0 
        (x * (1 - 1 / 3) - 2) / 2 = 5 
        x = 18
```

## 6. `gsm8k_15`

```yaml
id: "gsm8k_15"
source: "GSM8K"
topic: "grade-school arithmetic word problem"
difficulty: "test"
natural_language_idea: "Name the quantities in the word problem, encode the arithmetic relationships, and check the final numerical result."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
claim:
    prove:
        forall contempory_per, jazz_per, actual_jazz_per, hiphop_per, hiphop N:
            contempory_per = 0.2
            jazz_per = 0.25
            actual_jazz_per = (1 - contempory_per) * jazz_per
            hiphop_per = 1 - contempory_per - actual_jazz_per
            hiphop = hiphop_per * 100
            =>:
                contempory_per = 0.2 
        jazz_per = 0.25 
        actual_jazz_per = (1 - contempory_per) * jazz_per 
        hiphop_per = 1 - contempory_per - actual_jazz_per 
        hiphop = hiphop_per * 100 
        hiphop = 60
    actual_jazz_per = (1 - 0.2) * 0.25 = 0.8 * 0.25 = 0.2
    hiphop_per = 1 - 0.2 - 0.2 = 0.6
    hiphop = 0.6 * 100 = 60
```

## 7. `gsm8k_3`

```yaml
id: "gsm8k_3"
source: "GSM8K"
topic: "grade-school arithmetic word problem"
difficulty: "test"
natural_language_idea: "Name the quantities in the word problem, encode the arithmetic relationships, and check the final numerical result."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
claim:
    prove:
        forall buy_cost, repair_cost, increase_value, old_value, new_value, profit R:
            buy_cost = 80000
            repair_cost = 50000
            increase_value = 1.5
            old_value = buy_cost + repair_cost
            new_value = buy_cost * (1 + increase_value)
            profit = new_value - old_value
            =>:
                buy_cost = 80000 
        repair_cost = 50000 
        increase_value = 1.5 
        old_value = buy_cost + repair_cost 
        new_value = buy_cost * (1 + increase_value) 
        profit = new_value - old_value 
        profit = 70000
    old_value = 80000 + 50000 = 130000
    new_value = 80000 * (1 + 1.5) = 200000
    profit = 200000 - 130000 = 70000
```

## 8. `gsm8k_599`

```yaml
id: "gsm8k_599"
source: "GSM8K"
topic: "grade-school arithmetic word problem"
difficulty: "test"
natural_language_idea: "Name the quantities in the word problem, encode the arithmetic relationships, and check the final numerical result."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
claim:
    prove:
        forall quarters_count, dimes_count, nickels_count, pennies_count, quarter_value, dime_value, nickel_value, penny_value, gumball_cost, total_quarters, total_dimes, total_nickels, total_pennies, total_money, num_gumballs R:
            quarters_count = 8
            dimes_count = 6
            nickels_count = 14
            pennies_count = 15
            quarter_value = 0.25
            dime_value = 0.1
            nickel_value = 0.05
            penny_value = 0.01
            gumball_cost = 0.05
            total_quarters = quarters_count * quarter_value
            total_dimes = dimes_count * dime_value
            total_nickels = nickels_count * nickel_value
            total_pennies = pennies_count * penny_value
            total_money = total_quarters + total_dimes + total_nickels + total_pennies
            num_gumballs = total_money / gumball_cost
            =>:
                quarters_count = 8 
        dimes_count = 6 
        nickels_count = 14 
        pennies_count = 15 
        quarter_value = 0.25 
        dime_value = 0.1 
        nickel_value = 0.05 
        penny_value = 0.01 
        gumball_cost = 0.05 
        total_quarters = quarters_count * quarter_value 
        total_dimes = dimes_count * dime_value 
        total_nickels = nickels_count * nickel_value 
        total_pennies = pennies_count * penny_value 
        total_money = total_quarters + total_dimes + total_nickels + total_pennies 
        num_gumballs = total_money / gumball_cost 
        num_gumballs = 69
    total_quarters = 8 * 0.25 = 2.0
        
    total_dimes = 6 * 0.1 = 0.6
        
    total_nickels = 14 * 0.05 = 0.7
        
    total_pennies = 15 * 0.01 = 0.15
        
    total_money = 2.0 + 0.6 + 0.7 + 0.15 = 3.45
        
    num_gumballs = 3.45 / 0.05 = 69
```

## 9. `gsm8k_660`

```yaml
id: "gsm8k_660"
source: "GSM8K"
topic: "grade-school arithmetic word problem"
difficulty: "test"
natural_language_idea: "Name the quantities in the word problem, encode the arithmetic relationships, and check the final numerical result."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
claim:
    prove:
        forall price_almonds, price_walnuts, almonds_mix1_amount, walnuts_mix1_amount, almonds_mix2_amount, walnuts_mix2_amount, cost_almonds1, cost_walnuts1, cost_mix1, cost_almonds2, cost_walnuts2, cost_mix2, difference R:
            price_almonds = 10
            price_walnuts = 15
            almonds_mix1_amount = 1/2
            walnuts_mix1_amount = 1/3
            cost_almonds1 = price_almonds * almonds_mix1_amount
            cost_walnuts1 = price_walnuts * walnuts_mix1_amount
            cost_mix1 = cost_almonds1 + cost_walnuts1
            almonds_mix2_amount = 1/5
            walnuts_mix2_amount = 1/3
            cost_almonds2 = price_almonds * almonds_mix2_amount
            cost_walnuts2 = price_walnuts * walnuts_mix2_amount
            cost_mix2 = cost_almonds2 + cost_walnuts2
            difference = cost_mix1 - cost_mix2
            =>:
                price_almonds = 10 
        price_walnuts = 15 
        almonds_mix1_amount = 1/2 
        walnuts_mix1_amount = 1/3 
        cost_almonds1 = price_almonds * almonds_mix1_amount 
        cost_walnuts1 = price_walnuts * walnuts_mix1_amount 
        cost_mix1 = cost_almonds1 + cost_walnuts1 
        almonds_mix2_amount = 1/5 
        walnuts_mix2_amount = 1/3 
        cost_almonds2 = price_almonds * almonds_mix2_amount 
        cost_walnuts2 = price_walnuts * walnuts_mix2_amount 
        cost_mix2 = cost_almonds2 + cost_walnuts2 
        difference = cost_mix1 - cost_mix2 
        difference = 3
    cost_almonds1 = 10 * 0.5 = 5
    cost_walnuts1 = 15 * (1/3) = 5
    cost_mix1 = 5 + 5 = 10
    cost_almonds2 = 10 * 0.2 = 2
    cost_walnuts2 = 15 * (1/3) = 5
    cost_mix2 = 2 + 5 = 7
    difference = 10 - 7 = 3
```

## 10. `gsm8k_747`

```yaml
id: "gsm8k_747"
source: "GSM8K"
topic: "grade-school arithmetic word problem"
difficulty: "test"
natural_language_idea: "Name the quantities in the word problem, encode the arithmetic relationships, and check the final numerical result."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
claim:
    prove:
        forall adult_count, child_count, first_adult_price, first_child_price, second_adult_price, second_child_price, first_adult_total, first_child_total, first_total, second_adult_total, second_child_total, second_total, savings N_pos:
            adult_count = 2
            child_count = 2
            first_adult_price = 26
            first_child_price = 12
            second_adult_price = 14
            second_child_price = 10

            first_adult_total = adult_count * first_adult_price
            first_child_total = child_count * first_child_price
            first_total = first_adult_total + first_child_total

            second_adult_total = adult_count * second_adult_price
            second_child_total = child_count * second_child_price
            second_total = second_adult_total + second_child_total

            savings = first_total - second_total

            =>:
                adult_count = 2 
        child_count = 2 
        first_adult_price = 26 
        first_child_price = 12 
        second_adult_price = 14 
        second_child_price = 10 
        first_adult_total = adult_count * first_adult_price 
        first_child_total = child_count * first_child_price 
        first_total = first_adult_total + first_child_total 
        second_adult_total = adult_count * second_adult_price 
        second_child_total = child_count * second_child_price 
        second_total = second_adult_total + second_child_total 
        savings = first_total - second_total 
        savings = 28
    first_adult_total = 2 * 26 = 52
        
    first_child_total = 2 * 12 = 24
        
    first_total = 52 + 24 = 76
        
    second_adult_total = 2 * 14 = 28
        
    second_child_total = 2 * 10 = 20
        
    second_total = 28 + 20 = 48
        
    savings = 76 - 48 = 28
```

## 11. `gsm8k_797`

```yaml
id: "gsm8k_797"
source: "GSM8K"
topic: "grade-school arithmetic word problem"
difficulty: "test"
natural_language_idea: "Name the quantities in the word problem, encode the arithmetic relationships, and check the final numerical result."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
claim:
    prove:
        forall initial_employees, hires_per_month, salary_per_employee, total_month1, salary_month1, total_month2, salary_month2, total_month3, salary_month3, total_salary N_pos:
            initial_employees = 200
            hires_per_month = 20
            salary_per_employee = 4000
            total_month1 = initial_employees + hires_per_month
            salary_month1 = total_month1 * salary_per_employee
            total_month2 = total_month1 + hires_per_month
            salary_month2 = total_month2 * salary_per_employee
            total_month3 = total_month2 + hires_per_month
            salary_month3 = total_month3 * salary_per_employee
            total_salary = salary_month1 + salary_month2 + salary_month3
            =>:
                initial_employees = 200 
        hires_per_month = 20 
        salary_per_employee = 4000 
        total_month1 = initial_employees + hires_per_month 
        salary_month1 = total_month1 * salary_per_employee 
        total_month2 = total_month1 + hires_per_month 
        salary_month2 = total_month2 * salary_per_employee 
        total_month3 = total_month2 + hires_per_month 
        salary_month3 = total_month3 * salary_per_employee 
        total_salary = salary_month1 + salary_month2 + salary_month3 
        total_salary = 2880000
    total_month1 = 200 + 20 = 220
        
    salary_month1 = 220 * 4000 = 880000
        
    total_month2 = 220 + 20 = 240
        
    salary_month2 = 240 * 4000 = 960000
        
    total_month3 = 240 + 20 = 260
        
    salary_month3 = 260 * 4000 = 1040000
        
    total_salary = 880000 + 960000 + 1040000 = 2880000
```

## 12. `gsm8k_8`

```yaml
id: "gsm8k_8"
source: "GSM8K"
topic: "grade-school arithmetic word problem"
difficulty: "test"
natural_language_idea: "Name the quantities in the word problem, encode the arithmetic relationships, and check the final numerical result."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
claim:
    prove:
        forall file_size, download_speed, downloaded_percentage, first_download_time, update_time, total_time R:
            file_size = 200
            download_speed = 2
            downloaded_percentage = 0.4
            update_time = 20
            first_download_time = file_size * downloaded_percentage / download_speed
            total_time = first_download_time + update_time + file_size / download_speed
            =>:
                file_size = 200 
        download_speed = 2 
        downloaded_percentage = 0.4 
        update_time = 20 
        first_download_time = file_size * downloaded_percentage / download_speed 
        total_time = first_download_time + update_time + file_size / download_speed 
        total_time = 160
    first_download_time = (200 * 0.4) / 2 = 40
    total_time = 40 + 20 + 200 / 2 = 160
```

## 13. `gsm8k_807`

```yaml
id: "gsm8k_807"
source: "GSM8K"
topic: "grade-school arithmetic word problem"
difficulty: "test"
natural_language_idea: "Name the quantities in the word problem, encode the arithmetic relationships, and check the final numerical result."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
claim:
    prove:
        forall third_passed, third_total, fourth_passed, fourth_total, fifth_total, fourth_pass_rate, fifth_pass_rate, fifth_passed, total_passed, total_students, overall_pass_rate R:
            third_passed = 340
            third_total = 500
            fourth_passed = 40
            fourth_total = 100
            fifth_total = 400
            fourth_pass_rate = fourth_passed / fourth_total
            fifth_pass_rate = fourth_pass_rate * 2
            fifth_passed = fifth_pass_rate * fifth_total
            total_passed = third_passed + fourth_passed + fifth_passed
            total_students = third_total + fourth_total + fifth_total
            overall_pass_rate = total_passed / total_students * 100
            =>:
                third_passed = 340 
        third_total = 500 
        fourth_passed = 40 
        fourth_total = 100 
        fifth_total = 400 
        fourth_pass_rate = fourth_passed / fourth_total 
        fifth_pass_rate = fourth_pass_rate * 2 
        fifth_passed = fifth_pass_rate * fifth_total 
        total_passed = third_passed + fourth_passed + fifth_passed 
        total_students = third_total + fourth_total + fifth_total 
        overall_pass_rate = total_passed / total_students * 100 
        overall_pass_rate = 70
    fourth_pass_rate = 40 / 100 = 0.4
        
    fifth_pass_rate = 0.4 * 2 = 0.8
        
    fifth_passed = 0.8 * 400 = 320
        
    total_passed = 340 + 40 + 320 = 700
        
    total_students = 500 + 100 + 400 = 1000
        
    overall_pass_rate = 700 / 1000 * 100 = 70
```

## 14. `gsm8k_815`

```yaml
id: "gsm8k_815"
source: "GSM8K"
topic: "grade-school arithmetic word problem"
difficulty: "test"
natural_language_idea: "Name the quantities in the word problem, encode the arithmetic relationships, and check the final numerical result."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
claim:
    prove:
        forall jack_play_minutes, worse_friends_count, cost_per_quarter, total_hours, better_multiplier, jack_insertions_per_hour, worse_insertions_total, better_insertions_per_hour, jack_cost_per_hour, worse_cost_per_hour, better_cost_per_hour, total_cost_per_hour, total_cost R:
            jack_play_minutes = 20
            worse_friends_count = 2
            cost_per_quarter = 0.25
            total_hours = 4
            better_multiplier = 1.5

            jack_insertions_per_hour = 60 / jack_play_minutes
            worse_insertions_total = jack_insertions_per_hour * worse_friends_count
            better_insertions_per_hour = jack_insertions_per_hour / better_multiplier

            jack_cost_per_hour = jack_insertions_per_hour * cost_per_quarter
            worse_cost_per_hour = worse_insertions_total * cost_per_quarter
            better_cost_per_hour = better_insertions_per_hour * cost_per_quarter

            total_cost_per_hour = jack_cost_per_hour + worse_cost_per_hour + better_cost_per_hour
            total_cost = total_cost_per_hour * total_hours
            =>:
                jack_play_minutes = 20 
        worse_friends_count = 2 
        cost_per_quarter = 0.25 
        total_hours = 4 
        better_multiplier = 1.5 
        jack_insertions_per_hour = 60 / jack_play_minutes 
        worse_insertions_total = jack_insertions_per_hour * worse_friends_count 
        better_insertions_per_hour = jack_insertions_per_hour / better_multiplier 
        jack_cost_per_hour = jack_insertions_per_hour * cost_per_quarter 
        worse_cost_per_hour = worse_insertions_total * cost_per_quarter 
        better_cost_per_hour = better_insertions_per_hour * cost_per_quarter 
        total_cost_per_hour = jack_cost_per_hour + worse_cost_per_hour + better_cost_per_hour 
        total_cost = total_cost_per_hour * total_hours 
        total_cost = 11
    jack_insertions_per_hour = 60 / 20 = 3

    worse_insertions_total = 3 * 2 = 6

    better_insertions_per_hour = 3 / 1.5 = 2

    jack_cost_per_hour = 3 * 0.25 = 0.75

    worse_cost_per_hour = 6 * 0.25 = 1.5

    better_cost_per_hour = 2 * 0.25 = 0.5

    total_cost_per_hour = 0.75 + 1.5 + 0.5 = 2.75

    total_cost = 2.75 * 4 = 11
```

## 15. `gsm8k_831`

```yaml
id: "gsm8k_831"
source: "GSM8K"
topic: "grade-school arithmetic word problem"
difficulty: "test"
natural_language_idea: "Name the quantities in the word problem, encode the arithmetic relationships, and check the final numerical result."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
claim:
    prove:
        forall videos_per_week, min_per_video, recording_time_per_week, song_hours_per_week, min_per_hour, song_min_per_week, makeup_min_per_day, makeup_days_per_week, makeup_time_per_week, total_week_time, weeks_per_month, total_time R:
            videos_per_week = 18
            min_per_video = 4
            recording_time_per_week = videos_per_week * min_per_video
            song_hours_per_week = 2
            min_per_hour = 60
            song_min_per_week = song_hours_per_week * min_per_hour
            makeup_min_per_day = 15
            makeup_days_per_week = 6
            makeup_time_per_week = makeup_min_per_day * makeup_days_per_week
            total_week_time = recording_time_per_week + song_min_per_week + makeup_time_per_week
            weeks_per_month = 4
            total_time = total_week_time * weeks_per_month
            =>:
                videos_per_week = 18 
        min_per_video = 4 
        recording_time_per_week = videos_per_week * min_per_video 
        song_hours_per_week = 2 
        min_per_hour = 60 
        song_min_per_week = song_hours_per_week * min_per_hour 
        makeup_min_per_day = 15 
        makeup_days_per_week = 6 
        makeup_time_per_week = makeup_min_per_day * makeup_days_per_week 
        total_week_time = recording_time_per_week + song_min_per_week + makeup_time_per_week 
        weeks_per_month = 4 
        total_time = total_week_time * weeks_per_month 
        total_time = 1128
    recording_time_per_week = 18 * 4 = 72
        
    song_min_per_week = 2 * 60 = 120
        
    makeup_time_per_week = 15 * 6 = 90
        
    total_week_time = 72 + 120 + 90 = 282
        
    total_time = 282 * 4 = 1128
```

## 16. `gsm8k_85`

```yaml
id: "gsm8k_85"
source: "GSM8K"
topic: "grade-school arithmetic word problem"
difficulty: "test"
natural_language_idea: "Name the quantities in the word problem, encode the arithmetic relationships, and check the final numerical result."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
claim:
    prove:
        forall games, wins, losses N_pos:
            games = 22
            wins = losses + 8
            games = wins + losses
            losses + 8 + losses = 22
            2 * losses = 14
            losses = 7
            wins = 15
            =>:
                games = 22 
        wins = 15 
        losses = 7
```

## 17. `gsm8k_883`

```yaml
id: "gsm8k_883"
source: "GSM8K"
topic: "grade-school arithmetic word problem"
difficulty: "test"
natural_language_idea: "Name the quantities in the word problem, encode the arithmetic relationships, and check the final numerical result."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
claim:
    prove:
        forall bacon_packs, bacon_total_cost, bacon_per_pack, chicken_packs, chicken_per_pack, chicken_total_cost, strawberry_packs, strawberry_per_pack, strawberry_total_cost, apple_packs, apple_per_pack, apple_total_cost, total_spent, budget, money_left R:
            bacon_packs = 5
            bacon_total_cost = 10
            bacon_per_pack = bacon_total_cost / bacon_packs
            chicken_packs = 6
            chicken_per_pack = bacon_per_pack * 2
            chicken_total_cost = chicken_packs * chicken_per_pack
            strawberry_packs = 3
            strawberry_per_pack = 4
            strawberry_total_cost = strawberry_packs * strawberry_per_pack
            apple_packs = 7
            apple_per_pack = strawberry_per_pack / 2
            apple_total_cost = apple_packs * apple_per_pack
            total_spent = bacon_total_cost + chicken_total_cost + strawberry_total_cost + apple_total_cost
            budget = 65
            money_left = budget - total_spent

            =>:
                bacon_packs = 5 
        bacon_total_cost = 10 
        bacon_per_pack = bacon_total_cost / bacon_packs 
        chicken_packs = 6 
        chicken_per_pack = bacon_per_pack * 2 
        chicken_total_cost = chicken_packs * chicken_per_pack 
        strawberry_packs = 3 
        strawberry_per_pack = 4 
        strawberry_total_cost = strawberry_packs * strawberry_per_pack 
        apple_packs = 7 
        apple_per_pack = strawberry_per_pack / 2 
        apple_total_cost = apple_packs * apple_per_pack 
        total_spent = bacon_total_cost + chicken_total_cost + strawberry_total_cost + apple_total_cost 
        budget = 65 
        money_left = budget - total_spent 
        money_left = 5
    bacon_per_pack = 10 / 5 = 2

    chicken_per_pack = 2 * 2 = 4

    chicken_total_cost = 6 * 4 = 24

    strawberry_total_cost = 3 * 4 = 12

    apple_per_pack = 4 / 2 = 2

    apple_total_cost = 7 * 2 = 14

    total_spent = 10 + 24 + 12 + 14 = 60

    money_left = 65 - 60 = 5
```

## 18. `gsm8k_9`

```yaml
id: "gsm8k_9"
source: "GSM8K"
topic: "grade-school arithmetic word problem"
difficulty: "test"
natural_language_idea: "Name the quantities in the word problem, encode the arithmetic relationships, and check the final numerical result."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
claim:
    prove:
        forall first_time, first_speed, first_distance, return_tot_time, remaining_distance, jam_time, half_hour, half_hour_distance, remaining_time, remaining_speed, final_remaining_distance, half_hour_speed R:
            first_time = 3
            first_speed = 60
            return_tot_time = 4
            jam_time = 2
            half_hour = 0.5
            half_hour_speed = 30
            remaining_speed = 80
            first_distance = first_time * first_speed
            remaining_time = return_tot_time - jam_time - half_hour
            half_hour_distance = half_hour * half_hour_speed
            remaining_distance = remaining_time * remaining_speed
            final_remaining_distance = first_distance - half_hour_distance - remaining_distance
            =>:
                first_time = 3 
        first_speed = 60 
        return_tot_time = 4 
        jam_time = 2 
        half_hour = 0.5 
        half_hour_speed = 30 
        remaining_speed = 80 
        first_distance = first_time * first_speed 
        remaining_time = return_tot_time - jam_time - half_hour 
        half_hour_distance = half_hour * half_hour_speed 
        remaining_distance = remaining_time * remaining_speed 
        final_remaining_distance = first_distance - half_hour_distance - remaining_distance 
        final_remaining_distance = 45
    first_distance = 3 * 60 = 180
    remaining_time = 4 - 2 - 0.5 = 1.5
    half_hour_distance = 0.5 * 30 = 15
    remaining_distance = 1.5 * 80 = 120
    final_remaining_distance = 180 - 15 - 120 = 45
```

## 19. `gsm8k_927`

```yaml
id: "gsm8k_927"
source: "GSM8K"
topic: "grade-school arithmetic word problem"
difficulty: "test"
natural_language_idea: "Name the quantities in the word problem, encode the arithmetic relationships, and check the final numerical result."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
claim:
    prove:
        forall monthly_allowance, fri_sat_ticket_cost, other_day_ticket_cost, popcorn_cost, candy_cost, fri_sat_movies, other_movies, popcorn_previous, candy_previous, total_fri_sat_cost, total_other_cost, total_popcorn_previous, total_candy_previous, total_spent_previous, last_popcorn, last_candy, snack_cost, remaining_after_spent, remaining_after_snacks, movies_last_night N_pos:
            monthly_allowance = 150
            fri_sat_ticket_cost = 10
            other_day_ticket_cost = 7
            popcorn_cost = 8
            candy_cost = 2
            fri_sat_movies = 5
            other_movies = 8
            popcorn_previous = 2
            candy_previous = 4
            last_popcorn = 1
            last_candy = 1
            total_fri_sat_cost = fri_sat_movies * fri_sat_ticket_cost
            total_other_cost = other_movies * other_day_ticket_cost
            total_popcorn_previous = popcorn_previous * popcorn_cost
            total_candy_previous = candy_previous * candy_cost
            total_spent_previous = total_fri_sat_cost + total_other_cost + total_popcorn_previous + total_candy_previous
            snack_cost = last_popcorn * popcorn_cost + last_candy * candy_cost
            remaining_after_spent = monthly_allowance - total_spent_previous
            remaining_after_snacks = remaining_after_spent - snack_cost
            movies_last_night = remaining_after_snacks / fri_sat_ticket_cost
            =>:
                monthly_allowance = 150 
        fri_sat_ticket_cost = 10 
        other_day_ticket_cost = 7 
        popcorn_cost = 8 
        candy_cost = 2 
        fri_sat_movies = 5 
        other_movies = 8 
        popcorn_previous = 2 
        candy_previous = 4 
        last_popcorn = 1 
        last_candy = 1 
        total_fri_sat_cost = fri_sat_movies * fri_sat_ticket_cost 
        total_other_cost = other_movies * other_day_ticket_cost 
        total_popcorn_previous = popcorn_previous * popcorn_cost 
        total_candy_previous = candy_previous * candy_cost 
        total_spent_previous = total_fri_sat_cost + total_other_cost + total_popcorn_previous + total_candy_previous 
        snack_cost = last_popcorn * popcorn_cost + last_candy * candy_cost 
        remaining_after_spent = monthly_allowance - total_spent_previous 
        remaining_after_snacks = remaining_after_spent - snack_cost 
        movies_last_night = remaining_after_snacks / fri_sat_ticket_cost 
        movies_last_night = 1
    total_fri_sat_cost = 5 * 10 = 50
        
    total_other_cost = 8 * 7 = 56
        
    total_popcorn_previous = 2 * 8 = 16
        
    total_candy_previous = 4 * 2 = 8
        
    total_spent_previous = 50 + 56 + 16 + 8 = 130
        
    snack_cost = 1*8 + 1*2 = 10
        
    remaining_after_spent = 150 - 130 = 20
        
    remaining_after_snacks = 20 - 10 = 10
        
    movies_last_night = 10 / 10 = 1
```

## 20. `gsm8k_96`

```yaml
id: "gsm8k_96"
source: "GSM8K"
topic: "grade-school arithmetic word problem"
difficulty: "test"
natural_language_idea: "Name the quantities in the word problem, encode the arithmetic relationships, and check the final numerical result."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
claim:
    prove:
        forall students, boys_ratio, boys, girls, scout_ratio, in_scout, not_scout N_pos:
            students = 200
            boys_ratio = 2 / 5
            boys = students * boys_ratio
            girls = students - boys
            scout_ratio = 2 / 3
            in_scout = girls * scout_ratio
            not_scout = girls - in_scout
            =>:
                students = 200 
        boys_ratio = 2 / 5 
        boys = students * boys_ratio 
        girls = students - boys 
        scout_ratio = 2 / 3 
        in_scout = girls * scout_ratio 
        not_scout = girls - in_scout 
        not_scout = 40
    boys = 200 * (2 / 5) = 80
    girls = 200 - 80 = 120
    in_scout = 120 * (2 / 3) = 80
    not_scout = 120 - 80 = 40
```
