# Math23K

Chinese arithmetic word-problem derivations translated into explicit Litex quantity relationships.

Each item gives the mathematical idea first, then the Litex code that checks it.

## 1. `Math23k_10418`

```yaml
id: "Math23k_10418"
source: "Math23K"
topic: "Chinese arithmetic word problem"
difficulty: "mixed"
natural_language_idea: "Translate the arithmetic word problem into named quantities and verify the resulting calculation chain."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Representative checked example for this gallery."
```

```litex
claim:
    prove:
        forall total_length, week1_frac, week2_frac, week3_frac, week1_length, week2_length, week3_length, total_week23_length, total_completed_length, remaining_length, remaining_fraction R:
            total_length = 1000
            week1_frac = 1/7
            week2_frac = 2/5
            week3_frac = 2/5

            week1_length = total_length * week1_frac
            week2_length = total_length * week2_frac
            week3_length = total_length * week3_frac

            total_week23_length = week2_length + week3_length
            total_completed_length = week1_length + total_week23_length

            remaining_length = total_length - total_completed_length
            remaining_fraction = remaining_length / total_length
            week1_length = 1000 * (1/7) = 1000 / 7

            week2_length = 1000 * (2/5) = 400

            week3_length = 1000 * (2/5) = 400

            total_week23_length = 400 + 400 = 800

            total_completed_length = 1000/7 + 800
            800 = (800 * 7) / 7
            total_completed_length = 1000/7 + (800 * 7) / 7 = (1000 + 5600) / 7 = 6600 / 7

            remaining_length = 1000 - 6600/7
            1000 = (1000 * 7) / 7
            remaining_length = (1000 * 7) / 7 - 6600/7 = 7000/7 - 6600/7 = (7000 - 6600)/7 = 400/7

            remaining_fraction = (400/7) / 1000 = 400 / 7000 = 4 / 70 = 2 / 35
            =>:
                total_length = 1000 
                week1_frac = 1/7 
                week2_frac = 2/5 
                week3_frac = 2/5 
                week1_length = total_length * week1_frac 
                week2_length = total_length * week2_frac 
                week3_length = total_length * week3_frac 
                total_week23_length = week2_length + week3_length 
                total_completed_length = week1_length + total_week23_length 
                remaining_length = total_length - total_completed_length 
                remaining_fraction = remaining_length / total_length 
                remaining_fraction = 2/35
```

## 2. `Math23k_10892`

```yaml
id: "Math23k_10892"
source: "Math23K"
topic: "Chinese arithmetic word problem"
difficulty: "mixed"
natural_language_idea: "Translate the arithmetic word problem into named quantities and verify the resulting calculation chain."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Representative checked example for this gallery."
```

```litex
claim:
    prove:
        forall price, cost, total_revenue1, total_cost1, profit1, total_revenue2, total_cost2, profit2 R:
            price - cost = 400
            total_revenue1 = 10 * (0.8 * price)
            total_cost1 = 10 * cost
            profit1 = total_revenue1 - total_cost1
            total_revenue2 = 15 * (price - 300)
            total_cost2 = 15 * cost
            profit2 = total_revenue2 - total_cost2
            profit1 = profit2
            total_revenue1 = 10 * (0.8 * price) = (10 * 0.8) * price = 8 * price

            total_cost1 = 10 * cost

            profit1 = total_revenue1 - total_cost1 = 8 * price - 10 * cost

            total_revenue2 = 15 * (price - 300) = 15 * price - 15 * 300 = 15 * price - 4500

            total_cost2 = 15 * cost

            profit2 = total_revenue2 - total_cost2 = 15 * price - 4500 - 15 * cost

            price - cost = 400
            price - cost + cost = 400 + cost
            price = 400 + cost

            price - 400 = cost
            cost = price - 400

            profit1 = 8 * price - 10 * cost = 8 * price - 10 * (price - 400)
            10 * (price - 400) = 10 * price - 10 * 400
            10 * (price - 400) = 10 * price - 4000
            profit1 = 8 * price - (10 * price - 4000) = 8 * price - 10 * price + 4000 = -2 * price + 4000

            profit2 = 15 * price - 4500 - 15 * cost = 15 * price - 4500 - 15 * (price - 400)
            15 * (price - 400) = 15 * price - 15 * 400
            15 * (price - 400) = 15 * price - 6000
            profit2 = 15 * price - 4500 - (15 * price - 6000) = 15 * price - 4500 - 15 * price + 6000 = 1500

            profit1 = profit2
            -2 * price + 4000 = 1500
            -2 * price = 1500 - 4000
            -2 * price = -2500
            price = (-2500) / (-2) = 1250
            =>:
                price - cost = 400 
                total_revenue1 = 10 * (0.8 * price) 
                total_cost1 = 10 * cost 
                profit1 = total_revenue1 - total_cost1 
                total_revenue2 = 15 * (price - 300) 
                total_cost2 = 15 * cost 
                profit2 = total_revenue2 - total_cost2 
                profit1 = profit2 
                price = 1250
```

## 3. `Math23k_12388`

```yaml
id: "Math23k_12388"
source: "Math23K"
topic: "Chinese arithmetic word problem"
difficulty: "mixed"
natural_language_idea: "Translate the arithmetic word problem into named quantities and verify the resulting calculation chain."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Representative checked example for this gallery."
```

```litex
claim:
    prove:
        forall total_students, jump_rope_yes, jump_rope_no, shuttlecock_yes, shuttlecock_no, both_yes, neither_yes R:
            total_students = 50
            jump_rope_yes = 4 * (total_students / 5)
            jump_rope_no = total_students / 5
            shuttlecock_yes = 3 * (total_students / 5)
            shuttlecock_no = 2 * (total_students / 5)
            both_yes = 25
            neither_yes = total_students - ((jump_rope_yes - both_yes) + (shuttlecock_yes - both_yes) + both_yes)
            jump_rope_yes = 4 * (50 / 5) = 40
            jump_rope_no = 50 / 5 = 10
            shuttlecock_yes = 3 * (50 / 5) = 30
            shuttlecock_no = 2 * (50 / 5) = 20
            neither_yes = 50 - ((40 - 25) + (30 - 25) + 25) = 50 - (15 + 5 + 25) = 5
            =>:
                total_students = 50 
                jump_rope_yes = 4 * (total_students / 5) 
                jump_rope_no = total_students / 5 
                shuttlecock_yes = 3 * (total_students / 5) 
                shuttlecock_no = 2 * (total_students / 5) 
                both_yes = 25 
                neither_yes = total_students - ((jump_rope_yes - both_yes) + (shuttlecock_yes - both_yes) + both_yes) 
                neither_yes = 5
```

## 4. `Math23k_14305`

```yaml
id: "Math23k_14305"
source: "Math23K"
topic: "Chinese arithmetic word problem"
difficulty: "mixed"
natural_language_idea: "Translate the arithmetic word problem into named quantities and verify the resulting calculation chain."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Representative checked example for this gallery."
```

```litex
claim:
    prove:
        forall big_car_count, big_trips, big_total, small_car_count, small_trips, small_total, total_coal, big_per_car_per_trip, small_per_car_per_trip, combined_per_trip, trips R:
            big_car_count = 4
            big_trips = 5
            big_total = 80
            small_car_count = 3
            small_trips = 8
            small_total = 72
            total_coal = 350
            big_per_car_per_trip = big_total / (big_car_count * big_trips)
            small_per_car_per_trip = small_total / (small_car_count * small_trips)
            combined_per_trip = big_per_car_per_trip + small_per_car_per_trip
            trips = total_coal / combined_per_trip
            big_per_car_per_trip = 80 / (4 * 5) = 80 / 20 = 4
            small_per_car_per_trip = 72 / (3 * 8) = 72 / 24 = 3
            combined_per_trip = 4 + 3 = 7
            trips = 350 / 7 = 50
            =>:
                big_car_count = 4 
                big_trips = 5 
                big_total = 80 
                small_car_count = 3 
                small_trips = 8 
                small_total = 72 
                total_coal = 350 
                big_per_car_per_trip = big_total / (big_car_count * big_trips) 
                small_per_car_per_trip = small_total / (small_car_count * small_trips) 
                combined_per_trip = big_per_car_per_trip + small_per_car_per_trip 
                trips = total_coal / combined_per_trip 
                trips = 50
```

## 5. `Math23k_146`

```yaml
id: "Math23k_146"
source: "Math23K"
topic: "Chinese arithmetic word problem"
difficulty: "mixed"
natural_language_idea: "Translate the arithmetic word problem into named quantities and verify the resulting calculation chain."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Representative checked example for this gallery."
```

```litex
claim:
    prove:
        forall tank_length, tank_width, initial_water_height, final_water_height, iron_length, iron_width, initial_water_volume, final_water_volume, iron_volume, iron_height R:
            tank_length = 8
            tank_width = 6
            initial_water_height = 4
            final_water_height = 4.2
            iron_length = 3
            iron_width = 2
            initial_water_volume = tank_length * tank_width * initial_water_height
            final_water_volume = tank_length * tank_width * final_water_height
            iron_volume = final_water_volume - initial_water_volume = iron_length * iron_width * iron_height
            initial_water_volume = 8 * 6 * 4 = 192
            final_water_volume = 8 * 6 * 4.2 = 201.6
            iron_volume = 201.6 - 192 = 9.6 = 3 * 2 * iron_height
            6 * iron_height = 9.6
            iron_height = 9.6 / 6 = 1.6
            =>:
                tank_length = 8 
                tank_width = 6 
                initial_water_height = 4 
                final_water_height = 4.2 
                iron_length = 3 
                iron_width = 2 
                initial_water_volume = tank_length * tank_width * initial_water_height 
                final_water_volume = tank_length * tank_width * final_water_height 
                iron_volume = final_water_volume - initial_water_volume 
                iron_volume = iron_length * iron_width * iron_height 
                iron_height = 1.6
```

## 6. `Math23k_15770`

```yaml
id: "Math23k_15770"
source: "Math23K"
topic: "Chinese arithmetic word problem"
difficulty: "mixed"
natural_language_idea: "Translate the arithmetic word problem into named quantities and verify the resulting calculation chain."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Representative checked example for this gallery."
```

```litex
claim:
    prove:
        forall initial_mass, initial_conc, add_mass, add_conc, final_conc, initial_salt, add_salt, total_salt, total_mass R:
            initial_mass = 20
            initial_conc = 1/10
            add_conc = 3/10
            final_conc = 11/50
            initial_salt = initial_mass * initial_conc
            add_salt = add_mass * add_conc
            total_salt = initial_salt + add_salt
            total_mass = initial_mass + add_mass
            total_salt = total_mass * final_conc
            initial_salt = 20 * (1/10) = 2

            add_salt = add_mass * (3/10)

            total_salt = initial_salt + add_salt = 2 + add_mass * (3/10)

            total_mass = initial_mass + add_mass = 20 + add_mass

            total_salt = total_mass * final_conc = (20 + add_mass) * (11/50)

            2 + add_mass * (3/10) = (20 + add_mass) * (11/50)

            50 * (2 + add_mass * (3/10)) = 50 * ((20 + add_mass) * (11/50))

            100 + 15 * add_mass = 220 + 11 * add_mass

            (100 + 15 * add_mass) - 11 * add_mass = (220 + 11 * add_mass) - 11 * add_mass

            100 + 4 * add_mass = 220

            (100 + 4 * add_mass) - 100 = 220 - 100

            4 * add_mass = 220 - 100
            220 - 100 = 120
            4 * add_mass = 120
            add_mass = 120 / 4 = 30
            =>:
                initial_mass = 20 
                initial_conc = 1/10 
                add_conc = 3/10 
                final_conc = 11/50 
                initial_salt = initial_mass * initial_conc 
                add_salt = add_mass * add_conc 
                total_salt = initial_salt + add_salt 
                total_mass = initial_mass + add_mass 
                total_salt = total_mass * final_conc 
                add_mass = 30
```

## 7. `Math23k_16650`

```yaml
id: "Math23k_16650"
source: "Math23K"
topic: "Chinese arithmetic word problem"
difficulty: "mixed"
natural_language_idea: "Translate the arithmetic word problem into named quantities and verify the resulting calculation chain."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Representative checked example for this gallery."
```

```litex
claim:
    prove:
        forall hours_per_day_teamA, days_teamA, hours_per_day_teamB, days_teamB, total_hours_teamA, total_hours_teamB, efficiency_teamA, efficiency_teamB, combined_efficiency, required_hours_per_day R:
            hours_per_day_teamA = 6
            days_teamA = 4
            hours_per_day_teamB = 8
            days_teamB = 5
            total_hours_teamA = hours_per_day_teamA * days_teamA
            total_hours_teamB = hours_per_day_teamB * days_teamB
            efficiency_teamA = 1 / total_hours_teamA
            efficiency_teamB = 1 / total_hours_teamB
            combined_efficiency = efficiency_teamA + efficiency_teamB
            required_hours_per_day = (1 / 2) / combined_efficiency
            total_hours_teamA = 6 * 4 = 24
            total_hours_teamB = 8 * 5 = 40
            efficiency_teamA = 1 / 24
            efficiency_teamB = 1 / 40
            combined_efficiency = 1 / 24 + 1 / 40 = 5 / 120 + 3 / 120 = 8 / 120 = 1 / 15
            required_hours_per_day = (1 / 2) / (1 / 15) = (1 / 2) * 15 = 7.5
            =>:
                hours_per_day_teamA = 6 
                days_teamA = 4 
                hours_per_day_teamB = 8 
                days_teamB = 5 
                total_hours_teamA = hours_per_day_teamA * days_teamA 
                total_hours_teamB = hours_per_day_teamB * days_teamB 
                efficiency_teamA = 1 / total_hours_teamA 
                efficiency_teamB = 1 / total_hours_teamB 
                combined_efficiency = efficiency_teamA + efficiency_teamB 
                required_hours_per_day = (1 / 2) / combined_efficiency 
                required_hours_per_day = 7.5
```

## 8. `Math23k_17435`

```yaml
id: "Math23k_17435"
source: "Math23K"
topic: "Chinese arithmetic word problem"
difficulty: "mixed"
natural_language_idea: "Translate the arithmetic word problem into named quantities and verify the resulting calculation chain."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Representative checked example for this gallery."
```

```litex
claim:
    prove:
        forall work_total, efficiency_A, efficiency_B, efficiency_C, work_done_A, work_remaining, efficiency_total, days_needed R:
            work_total = 1
            efficiency_A = 1 / 20
            efficiency_B = 1 / 30
            efficiency_C = 1 / 15
            work_done_A = 8 * efficiency_A
            work_remaining = work_total - work_done_A
            efficiency_total = efficiency_A + efficiency_B + efficiency_C
            days_needed = work_remaining / efficiency_total
            efficiency_A = 1 / 20
            efficiency_B = 1 / 30
            efficiency_C = 1 / 15
            work_done_A = 8 * (1 / 20) = 8 / 20 = 2 / 5
            work_remaining = 1 - 2 / 5 = 3 / 5
            efficiency_total = (1 / 20) + (1 / 30) + (1 / 15)
            efficiency_total = (3 / 60) + (2 / 60) + (4 / 60) = 9 / 60 = 3 / 20
            days_needed = (3 / 5) / (3 / 20) = (3 / 5) * (20 / 3) = 4
            =>:
                work_total = 1 
                efficiency_A = 1 / 20 
                efficiency_B = 1 / 30 
                efficiency_C = 1 / 15 
                work_done_A = 8 * efficiency_A 
                work_remaining = work_total - work_done_A 
                efficiency_total = efficiency_A + efficiency_B + efficiency_C 
                days_needed = work_remaining / efficiency_total 
                days_needed = 4
```

## 9. `Math23k_17797`

```yaml
id: "Math23k_17797"
source: "Math23K"
topic: "Chinese arithmetic word problem"
difficulty: "mixed"
natural_language_idea: "Translate the arithmetic word problem into named quantities and verify the resulting calculation chain."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Representative checked example for this gallery."
```

```litex
claim:
    prove:
        forall train_length, tunnel_length, time_tunnel, freight_length, overlap_time, total_distance, v_train, overlap_distance, relative_speed, v_freight R:
            train_length = 125
            tunnel_length = 150
            time_tunnel = 5.5
            freight_length = 100
            overlap_time = 3
            total_distance = train_length + tunnel_length
            v_train = total_distance / time_tunnel
            overlap_distance = train_length + freight_length
            relative_speed = overlap_distance / overlap_time
            v_freight = relative_speed - v_train
            total_distance = 125 + 150 = 275
            v_train = 275 / 5.5 = 50
            overlap_distance = 125 + 100 = 225
            relative_speed = 225 / 3 = 75
            v_freight = 75 - 50 = 25
            =>:
                train_length = 125 
                tunnel_length = 150 
                time_tunnel = 5.5 
                freight_length = 100 
                overlap_time = 3 
                total_distance = train_length + tunnel_length 
                v_train = total_distance / time_tunnel 
                overlap_distance = train_length + freight_length 
                relative_speed = overlap_distance / overlap_time 
                v_freight = relative_speed - v_train 
                v_freight = 25
```

## 10. `Math23k_194`

```yaml
id: "Math23k_194"
source: "Math23K"
topic: "Chinese arithmetic word problem"
difficulty: "mixed"
natural_language_idea: "Translate the arithmetic word problem into named quantities and verify the resulting calculation chain."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Representative checked example for this gallery."
```

```litex
claim:
    prove:
        forall master_hours_per_day, master_days, master_total_hours, master_efficiency, apprentice_hours_per_day, apprentice_days, apprentice_total_hours, apprentice_efficiency, master_daily_work, apprentice_daily_work, total_daily_work, days R:
            master_hours_per_day = 8
            master_days = 15
            apprentice_hours_per_day = 9
            apprentice_days = 20
            master_total_hours = master_hours_per_day * master_days
            apprentice_total_hours = apprentice_hours_per_day * apprentice_days
            master_efficiency = 1 / master_total_hours
            apprentice_efficiency = 1 / apprentice_total_hours
            master_daily_work = 6 * master_efficiency
            apprentice_daily_work = 6 * apprentice_efficiency
            total_daily_work = master_daily_work + apprentice_daily_work
            days = 1 / total_daily_work
            master_total_hours = 8 * 15 = 120
            apprentice_total_hours = 9 * 20 = 180
            master_efficiency = 1 / 120
            apprentice_efficiency = 1 / 180
            master_daily_work = 6 * (1/120) = 6/120 = 1/20
            apprentice_daily_work = 6 * (1/180) = 6/180 = 1/30
            total_daily_work = 1/20 + 1/30 = 3/60 + 2/60 = 5/60 = 1/12
            days = 1 / (1/12) = 12
            =>:
                master_hours_per_day = 8 
                master_days = 15 
                apprentice_hours_per_day = 9 
                apprentice_days = 20 
                master_total_hours = master_hours_per_day * master_days 
                apprentice_total_hours = apprentice_hours_per_day * apprentice_days 
                master_efficiency = 1 / master_total_hours 
                apprentice_efficiency = 1 / apprentice_total_hours 
                master_daily_work = 6 * master_efficiency 
                apprentice_daily_work = 6 * apprentice_efficiency 
                total_daily_work = master_daily_work + apprentice_daily_work 
                days = 1 / total_daily_work 
                days = 12
```

## 11. `Math23k_19983`

```yaml
id: "Math23k_19983"
source: "Math23K"
topic: "Chinese arithmetic word problem"
difficulty: "mixed"
natural_language_idea: "Translate the arithmetic word problem into named quantities and verify the resulting calculation chain."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Representative checked example for this gallery."
```

```litex
claim:
    prove:
        forall total0, sugar_ratio, water_ratio, ratio_sum, sugar0, add_water, total_after_water, add_sugar, new_total R:
            total0 = 10
            sugar_ratio = 1
            water_ratio = 26
            ratio_sum = sugar_ratio + water_ratio
            sugar0 = total0 / ratio_sum
            add_water = 52
            total_after_water = total0 + add_water
            new_total = total_after_water + add_sugar
            27 * (sugar0 + add_sugar) = new_total
            ratio_sum = 1 + 26 = 27

            sugar0 = 10 / 27

            total_after_water = 10 + 52 = 62

            new_total = 62 + add_sugar

            27 * (sugar0 + add_sugar) = new_total
            27 * (10 / 27 + add_sugar) = 62 + add_sugar

            27 * (10 / 27) + 27 * add_sugar = 62 + add_sugar

            10 + 27 * add_sugar = 62 + add_sugar

            (10 + 27 * add_sugar) - add_sugar = (62 + add_sugar) - add_sugar

            10 + (27 * add_sugar - add_sugar) = (62 + add_sugar) - add_sugar

            10 + 26 * add_sugar = (62 + add_sugar) - add_sugar

            10 + 26 * add_sugar = 62 + (add_sugar - add_sugar)

            10 + 26 * add_sugar = 62

            (10 + 26 * add_sugar) - 10 = 62 - 10

            26 * add_sugar = 62 - 10

            26 * add_sugar = 52

            (26 * add_sugar) / 26 = 52 / 26

            add_sugar = 52 / 26

            add_sugar = 2
            =>:
                total0 = 10 
                sugar_ratio = 1 
                water_ratio = 26 
                ratio_sum = sugar_ratio + water_ratio 
                sugar0 = total0 / ratio_sum 
                add_water = 52 
                total_after_water = total0 + add_water 
                new_total = total_after_water + add_sugar 
                27 * (sugar0 + add_sugar) = new_total 
                add_sugar = 2
```

## 12. `Math23k_21988`

```yaml
id: "Math23k_21988"
source: "Math23K"
topic: "Chinese arithmetic word problem"
difficulty: "mixed"
natural_language_idea: "Translate the arithmetic word problem into named quantities and verify the resulting calculation chain."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Representative checked example for this gallery."
```

```litex
claim:
    prove:
        forall up_speed, down_speed, d, t_up, t_down, total_dist, total_time, frac1, frac2, sumfrac, avg_speed R:
            up_speed = 8
            down_speed = 12
            d > 0
            t_up = d / up_speed
            t_down = d / down_speed
            total_dist = d + d
            total_time = t_up + t_down
            frac1 = 1/8
            frac2 = 1/12
            sumfrac = frac1 + frac2
            total_time != 0
            avg_speed = total_dist / total_time
            t_up = d / 8
            t_down = d / 12
            total_dist = d + d
            total_time = d / 8 + d / 12
            sumfrac = 1/8 + 1/12
            1/8 = 3/24
            1/12 = 2/24
            sumfrac = 3/24 + 2/24 = 5/24
            total_time = d * sumfrac = d * (5/24)
            total_dist = 2 * d
            avg_speed = total_dist / total_time = (2 * d) / (d * (5/24))
            (2 * d) / (d * (5/24)) = (2 / (5/24)) * (d / d)
            d / d = 1
            2 / (5/24) = (2 * 24) / 5
            (2 * 24) / 5 = 48/5
            avg_speed = 48/5
            =>:
                up_speed = 8 
                down_speed = 12 
                d > 0 
                t_up = d / up_speed 
                t_down = d / down_speed 
                total_dist = d + d 
                total_time = t_up + t_down 
                frac1 = 1/8 
                frac2 = 1/12 
                sumfrac = frac1 + frac2 
                total_time != 0 
                avg_speed = total_dist / total_time 
                avg_speed = 48/5
```

## 13. `Math23k_22300`

```yaml
id: "Math23k_22300"
source: "Math23K"
topic: "Chinese arithmetic word problem"
difficulty: "mixed"
natural_language_idea: "Translate the arithmetic word problem into named quantities and verify the resulting calculation chain."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Representative checked example for this gallery."
```

```litex
claim:
    prove:
        forall cows1, days1, cows2, days2, cpd, total1, total2, g, initial_grass, max_cows R:
            cows1 = 24
            days1 = 6
            cows2 = 21
            days2 = 8
            cpd = 1

            total1 = cows1 * days1 * cpd
            total2 = cows2 * days2 * cpd

            total1 = initial_grass + days1 * g
            total2 = initial_grass + days2 * g

            max_cows = g
            total1 = 24 * 6 * 1 = 144

            total2 = 21 * 8 * 1 = 168

            initial_grass + 6 * g = total1
            initial_grass + 6 * g = 144

            initial_grass + 8 * g = total2
            initial_grass + 8 * g = 168

            2 * g = (initial_grass + 8 * g) - (initial_grass + 6 * g)
            2 * g = 168 - 144
            2 * g = 24

            g = 24 / 2 = 12

            6 * g = 6 * 12
            6 * g = 72

            initial_grass + 6 * g = 144
            initial_grass + 72 = 144
            initial_grass = 144 - 72 = 72

            max_cows = g = 12
            =>:
                cows1 = 24 
                days1 = 6 
                cows2 = 21 
                days2 = 8 
                cpd = 1 
                total1 = cows1 * days1 * cpd 
                total2 = cows2 * days2 * cpd 
                total1 = initial_grass + days1 * g 
                total2 = initial_grass + days2 * g 
                max_cows = g 
                max_cows = 12
```

## 14. `Math23k_22404`

```yaml
id: "Math23k_22404"
source: "Math23K"
topic: "Chinese arithmetic word problem"
difficulty: "mixed"
natural_language_idea: "Translate the arithmetic word problem into named quantities and verify the resulting calculation chain."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Representative checked example for this gallery."
```

```litex
claim:
    prove:
        forall D, v_c, v_h, delay_start, lead_finish, time_diff, t_c, t_h, lcm R:
            v_c = 72
            v_h = 90
            delay_start = 2
            lead_finish = 4
            time_diff = delay_start + lead_finish
            t_c = D / v_c
            t_h = D / v_h
            t_c = t_h + time_diff
            lcm = 360
            time_diff = 2 + 4 = 6
            t_c = D / 72
            t_h = D / 90
            t_c = t_h + 6
            lcm = 360
            lcm * t_c = lcm * (t_h + 6)
            lcm * (t_h + 6) = lcm * t_h + lcm * 6
            lcm * t_c = lcm * t_h + lcm * 6
            lcm * t_c = lcm * (D / 72)
            lcm * (D / 72) = (D / 72) * lcm
            (D / 72) * lcm = D * (lcm / 72)
            lcm / 72 = 360 / 72
            lcm / 72 = 5
            D * (lcm / 72) = D * 5
            D * 5 = 5 * D
            lcm * t_c = 5 * D
            lcm * t_h = lcm * (D / 90)
            lcm * (D / 90) = (D / 90) * lcm
            (D / 90) * lcm = D * (lcm / 90)
            lcm / 90 = 360 / 90
            lcm / 90 = 4
            D * (lcm / 90) = D * 4
            D * 4 = 4 * D
            lcm * t_h = 4 * D
            lcm * 6 = 360 * 6
            360 * 6 = 2160
            lcm * 6 = 2160
            5 * D = 4 * D + 2160
            5 * D - 4 * D = 2160
            D = 2160
            =>:
                v_c = 72 
                v_h = 90 
                delay_start = 2 
                lead_finish = 4 
                time_diff = delay_start + lead_finish 
                t_c = D / v_c 
                t_h = D / v_h 
                t_c = t_h + time_diff 
                lcm = 360 
                D = 2160
```

## 15. `Math23k_22755`

```yaml
id: "Math23k_22755"
source: "Math23K"
topic: "Chinese arithmetic word problem"
difficulty: "mixed"
natural_language_idea: "Translate the arithmetic word problem into named quantities and verify the resulting calculation chain."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Representative checked example for this gallery."
```

```litex
claim:
    prove:
        forall students_class1, students_class2, students_class3, teachers, student_ticket_price, teacher_ticket_price, total_students, total_teachers, total_student_cost, total_teacher_cost, total_cost R:
            students_class1 = 33
            students_class2 = 35
            students_class3 = 32
            teachers = 6
            student_ticket_price = 6
            teacher_ticket_price = 12
            total_students = students_class1 + students_class2 + students_class3
            total_teachers = teachers
            total_student_cost = total_students * student_ticket_price
            total_teacher_cost = total_teachers * teacher_ticket_price
            total_cost = total_student_cost + total_teacher_cost
            total_students = 33 + 35 + 32 = 100
            total_student_cost = 100 * 6 = 600
            total_teacher_cost = 6 * 12 = 72
            total_cost = 600 + 72 = 672
            =>:
                students_class1 = 33 
                students_class2 = 35 
                students_class3 = 32 
                teachers = 6 
                student_ticket_price = 6 
                teacher_ticket_price = 12 
                total_students = students_class1 + students_class2 + students_class3 
                total_teachers = teachers 
                total_student_cost = total_students * student_ticket_price 
                total_teacher_cost = total_teachers * teacher_ticket_price 
                total_cost = total_student_cost + total_teacher_cost 
                total_cost = 672
```

## 16. `Math23k_344`

```yaml
id: "Math23k_344"
source: "Math23K"
topic: "Chinese arithmetic word problem"
difficulty: "mixed"
natural_language_idea: "Translate the arithmetic word problem into named quantities and verify the resulting calculation chain."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Representative checked example for this gallery."
```

```litex
claim:
    prove:
        forall x, y R:
            y = x - (1/4) * x = (3/4) * x
            y + (1/6) * x = x - (1/6) * x + 2
            x - (1/6) * x = (5/6) * x
            y + (1/6) * x = (5/6) * x + 2
            (3/4) * x + (1/6) * x = (5/6) * x + 2
            (3/4) = (9/12)
            (1/6) = (2/12)
            (5/6) = (10/12)
            (9/12) * x + (2/12) * x = (10/12) * x + 2
            (9/12) * x + (2/12) * x = (11/12) * x
            (11/12) * x = (10/12) * x + 2
            (11/12) * x - (10/12) * x = 2
            (1/12) * x = 2
            x = 2 * 12
            y = x - (1/4) * x = (3/4) * x
            y + (1/6) * x = x - (1/6) * x + 2
            x - (1/6) * x = (5/6) * x
            y + (1/6) * x = (5/6) * x + 2
            (3/4) * x + (1/6) * x = (5/6) * x + 2
            (3/4) = (9/12)
            (1/6) = (2/12)
            (5/6) = (10/12)
            (9/12) * x + (2/12) * x = (10/12) * x + 2
            (9/12) * x + (2/12) * x = (11/12) * x
            (11/12) * x = (10/12) * x + 2
            (11/12) * x - (10/12) * x = 2
            (1/12) * x = 2
            x = 2 * 12 = 24
            =>:
                y = x - (1/4) * x 
                y = (3/4) * x 
                y + (1/6) * x = x - (1/6) * x + 2 
                x - (1/6) * x = (5/6) * x 
                y + (1/6) * x = (5/6) * x + 2 
                (3/4) * x + (1/6) * x = (5/6) * x + 2 
                (3/4) = (9/12) 
                (1/6) = (2/12) 
                (5/6) = (10/12) 
                (9/12) * x + (2/12) * x = (10/12) * x + 2 
                (9/12) * x + (2/12) * x = (11/12) * x 
                (11/12) * x = (10/12) * x + 2 
                (11/12) * x - (10/12) * x = 2 
                (1/12) * x = 2 
                x = 2 * 12 
                x = 24
```

## 17. `Math23k_6423`

```yaml
id: "Math23k_6423"
source: "Math23K"
topic: "Chinese arithmetic word problem"
difficulty: "mixed"
natural_language_idea: "Translate the arithmetic word problem into named quantities and verify the resulting calculation chain."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Representative checked example for this gallery."
```

```litex
claim:
    prove:
        forall dog_step, rabbit_step, dog_steps_per_cycle, rabbit_steps_per_cycle, dog_per_cycle, rabbit_per_cycle, gain_per_cycle, initial_distance, cycles, rabbit_total_steps, rabbit_total_distance R:
            dog_step = 2.8
            rabbit_step = 1.7
            dog_steps_per_cycle = 2
            rabbit_steps_per_cycle = 3
            initial_distance = 50
            dog_per_cycle = dog_step * dog_steps_per_cycle
            rabbit_per_cycle = rabbit_step * rabbit_steps_per_cycle
            gain_per_cycle = dog_per_cycle - rabbit_per_cycle
            cycles = initial_distance / gain_per_cycle
            rabbit_total_steps = cycles * rabbit_steps_per_cycle
            rabbit_total_distance = rabbit_total_steps * rabbit_step
            dog_per_cycle = 2.8 * 2 = 5.6
            rabbit_per_cycle = 1.7 * 3 = 5.1
            gain_per_cycle = 5.6 - 5.1 = 0.5
            cycles = 50 / 0.5 = 100
            rabbit_total_steps = 100 * 3 = 300
            rabbit_total_distance = 300 * 1.7 = 510
            =>:
                dog_step = 2.8 
                rabbit_step = 1.7 
                dog_steps_per_cycle = 2 
                rabbit_steps_per_cycle = 3 
                initial_distance = 50 
                dog_per_cycle = dog_step * dog_steps_per_cycle 
                rabbit_per_cycle = rabbit_step * rabbit_steps_per_cycle 
                gain_per_cycle = dog_per_cycle - rabbit_per_cycle 
                cycles = initial_distance / gain_per_cycle 
                rabbit_total_steps = cycles * rabbit_steps_per_cycle 
                rabbit_total_distance = rabbit_total_steps * rabbit_step 
                rabbit_total_distance = 510
```

## 18. `Math23k_7207`

```yaml
id: "Math23k_7207"
source: "Math23K"
topic: "Chinese arithmetic word problem"
difficulty: "mixed"
natural_language_idea: "Translate the arithmetic word problem into named quantities and verify the resulting calculation chain."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Representative checked example for this gallery."
```

```litex
claim:
    prove:
        forall integer_part, numerator_frac, denominator_frac, gcd, simplified_numerator, simplified_denominator, integer_numerator, total_numerator, total_denominator, result R:
            integer_part = 5
            numerator_frac = 25
            denominator_frac = 100
            gcd = 25
            simplified_numerator = numerator_frac / gcd
            simplified_denominator = denominator_frac / gcd
            integer_numerator = integer_part * simplified_denominator
            total_numerator = integer_numerator + simplified_numerator
            total_denominator = simplified_denominator
            result = total_numerator / total_denominator
            numerator_frac = 25
            denominator_frac = 100
            gcd = 25
            simplified_numerator = 25 / 25 = 1
            simplified_denominator = 100 / 25 = 4
            integer_part = 5
            integer_numerator = 5 * 4 = 20
            total_numerator = 20 + 1 = 21
            total_denominator = 4
            result = 21 / 4
            =>:
                integer_part = 5 
                numerator_frac = 25 
                denominator_frac = 100 
                gcd = 25 
                simplified_numerator = numerator_frac / gcd 
                simplified_denominator = denominator_frac / gcd 
                integer_numerator = integer_part * simplified_denominator 
                total_numerator = integer_numerator + simplified_numerator 
                total_denominator = simplified_denominator 
                result = total_numerator / total_denominator 
                result = 21/4
```

## 19. `Math23k_7912`

```yaml
id: "Math23k_7912"
source: "Math23K"
topic: "Chinese arithmetic word problem"
difficulty: "mixed"
natural_language_idea: "Translate the arithmetic word problem into named quantities and verify the resulting calculation chain."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Representative checked example for this gallery."
```

```litex
claim:
    prove:
        forall total_clothes, daily_original, total_days_original, first_days, done_first, remaining, daily_increase, daily_new, days_remaining, total_days_actual, days_ahead R:
            total_clothes = 1200
            daily_original = 100
            total_days_original = total_clothes / daily_original
            first_days = 4
            done_first = daily_original * first_days
            remaining = total_clothes - done_first
            daily_increase = 60
            daily_new = daily_original + daily_increase
            days_remaining = remaining / daily_new
            total_days_actual = first_days + days_remaining
            days_ahead = total_days_original - total_days_actual
            total_days_original = 1200 / 100 = 12
            done_first = 100 * 4 = 400
            remaining = 1200 - 400 = 800
            daily_new = 100 + 60 = 160
            days_remaining = 800 / 160 = 5
            total_days_actual = 4 + 5 = 9
            days_ahead = 12 - 9 = 3
            =>:
                total_clothes = 1200 
                daily_original = 100 
                total_days_original = total_clothes / daily_original 
                first_days = 4 
                done_first = daily_original * first_days 
                remaining = total_clothes - done_first 
                daily_increase = 60 
                daily_new = daily_original + daily_increase 
                days_remaining = remaining / daily_new 
                total_days_actual = first_days + days_remaining 
                days_ahead = total_days_original - total_days_actual 
                days_ahead = 3
```

## 20. `Math23k_9587`

```yaml
id: "Math23k_9587"
source: "Math23K"
topic: "Chinese arithmetic word problem"
difficulty: "mixed"
natural_language_idea: "Translate the arithmetic word problem into named quantities and verify the resulting calculation chain."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Representative checked example for this gallery."
```

```litex
claim:
    prove:
        forall denom, num1, num2, num3, num4, num5, num6, inner_num, total_num, simplified_numerator, simplified_denominator, result R:
            denom = 1260
            num1 = 4 * (denom / 3)
            num2 = 15 * (denom / 36)
            num3 = 9 * (denom / 20)
            num4 = 7 * (denom / 12)
            num5 = 11 * (denom / 30)
            num6 = 13 * (denom / 42)
            inner_num = num1 - num2 + num3 - num4
            total_num = inner_num - num5 + num6
            simplified_numerator = total_num / 15
            simplified_denominator = denom / 15
            result = simplified_numerator / simplified_denominator
            num1 = 4 * (1260 / 3) = 4 * 420 = 1680
            num2 = 15 * (1260 / 36) = 15 * 35 = 525
            num3 = 9 * (1260 / 20) = 9 * 63 = 567
            num4 = 7 * (1260 / 12) = 7 * 105 = 735
            num5 = 11 * (1260 / 30) = 11 * 42 = 462
            num6 = 13 * (1260 / 42) = 13 * 30 = 390
            inner_num = 1680 - 525 + 567 - 735 = 987
            total_num = 987 - 462 + 390 = 915
            simplified_numerator = 915 / 15 = 61
            simplified_denominator = 1260 / 15 = 84
            result = 61 / 84
            =>:
                denom = 1260 
                num1 = 4 * (denom / 3) 
                num2 = 15 * (denom / 36) 
                num3 = 9 * (denom / 20) 
                num4 = 7 * (denom / 12) 
                num5 = 11 * (denom / 30) 
                num6 = 13 * (denom / 42) 
                inner_num = num1 - num2 + num3 - num4 
                total_num = inner_num - num5 + num6 
                simplified_numerator = total_num / 15 
                simplified_denominator = denom / 15 
                result = simplified_numerator / simplified_denominator 
                result = 61 / 84
```
