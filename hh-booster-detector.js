// ==UserScript==
// @name            Hentai Heroes++ League Booster Detector Add-on
// @description     Adding detection of boosters to league.
// @version         0.2.5
// @match           https://*.hentaiheroes.com/*
// @match           https://nutaku.haremheroes.com/*
// @match           https://www.gayharem.com/*
// @match           https://nutaku.gayharem.com/*
// @match           https://*.comixharem.com/*
// @match           https://*.hornyheroes.com/*
// @match           https://*.pornstarharem.com/*
// @run-at          document-end
// @updateURL       https://raw.githubusercontent.com/zoop0kemon/hh-booster-detector/main/hh-booster-detector.js
// @downloadURL     https://raw.githubusercontent.com/zoop0kemon/hh-booster-detector/main/hh-booster-detector.js
// @grant           none
// @author          45026831(Numbers), zoopokemon
// ==/UserScript==

/*  ===========
     CHANGELOG
    =========== */
// 0.2.5: Fixing collection of opponent player equip data
// 0.2.4: Fixes for variable name and behavior changes after 22/03 update
// 0.2.3: Adding pending indication while profile data is being loaded
// 0.2.2: Adding tooltips on mobile
// 0.2.1: Fixing ginseng check in the corner-case where profile stats don't match snapshot
// 0.2.0: Changing stat collection to work with mythic items
// 0.1.14: Improving harem endurance bonus calculation now that the game calculates it properly
// 0.1.13: Taking ego dominance bonus into account now that it's incuded in the opponent's stats
// 0.1.12: Fixing ego check after game update
// 0.1.11: Adding PSH matcher for Weds official release
// 0.1.10: re added team girl counts when missing
// 0.1.9: Reversing sun and dominance attack bonuses to fix base stat estimates
// 0.1.8: Pre-empting change to playerLeaguesData currently being tested on TS. Using now-exposed opponent synergies to improve accuracy.
// 0.1.7: Applying the club bonus to harem level, fixing rainbow stat per level magic number
// 0.1.6: Emergency fixes for camelCase vars renamed to snake_case
// 0.1.5: Adding matcher for CxH
// 0.1.4: Accounting for element synergy bonuses in stats
// 0.1.3: Removing manual summing of girl stats, using totalPower value instead
// 0.1.2: Adding support for mobile
// 0.1.1: Adding back text stroke on boosted stats to be easier on the eyes. Adding matchers for GH
// 0.1.0: Major refactor around how results are displayed, slight boosts are shown in orange instead of full red, logs disabled by default with details moved into tooltips
// 0.0.17: Improving calculations in the estimate scenario using formulae from zoopokemon
// 0.0.16: Improving accuracy of monostat calculation by using both attack and harmony
// 0.0.15: Adding back chlorella checking in estimate scenario, cleaning up magic numbers into self-documenting code
// 0.0.14: Fixing bug in secondary and tertiary stats for display
// 0.0.13: Cleaning up the maths on estimations
// 0.0.12: If base stats not available, attempt to work backwards from derived stats, display estimates in stat tooltips
// 0.0.11: Making use of new tooltip data attribute
// 0.0.10: Removing unrounded value from cordy debug output
// 0.0.9: Fixing typo in Cordy check
// 0.0.8: Changing to match new calculations for BDSM
// 0.0.7: Setting an upper limit of 6 on the monostat count calculation
// 0.0.6: Adjusting Jujubes formula to more accurately reflect actual equipment stats
// 0.0.5: Adding booster icons in the table (after checks have run)
// 0.0.4: Adding detection for Jujubes
// 0.0.3: Adding detection for Ginseng
// 0.0.2: Updated Chlorella check to use Alpha's main stat instead of Alpha's Player Class stat
// 0.0.1: Initial version. Adding detection for Chlorella and Cordyceps

// Define jQuery
const { $, location } = window;
const LOGS_ENABLED = false

if (!$) {
    console.log('HH++ BOOSTER DETECTOR WARNING: No jQuery found. Probably an error page. Ending the script here');
    return;
}

// Define CSS
const sheet = (function () {
    const style = document.createElement('style')
    document.head.appendChild(style)
    return style.sheet
})()

const currentPage = location.pathname

const profileDataCache = {}

const HC = 1
const CH = 2
const KH = 3
const classRelationships = {
    [HC]: {
        s: KH,
        t: CH
    },
    [CH]: {
        s: HC,
        t: KH
    },
    [KH]: {
        s: CH,
        t: HC
    }
}

const lang = $('html')[0].lang.substring(0, 2)
let locale = 'fr'
if (lang === 'en') {
    locale = 'en'
}

// Magic numbers
const RAINBOW_STAT_PER_LEVEL = 7
const RAINBOW_HARM_PER_LEVEL = 9.1
const RAINBOW_HARM_BASE = 90
const MONOSTAT_PER_LEVEL = 11.15
const PRIMARY_PER_LEVEL = 9 + 30
const SECONDARY_PER_LEVEL = 7 + 30
const TERTIARY_PER_LEVEL = 5 + 30
const ENDURANCE_PER_PRIMARY = 4
const DEFENCE_PER_NON_PRIM = 0.25
const HARMONY_PER_NON_PRIM = 0.5
const MIN_POTENTIAL_MONOSTAT = 0
const MAX_POTENTIAL_MONOSTAT = 6
const HAREM_BONUS_PER_LVL = 52
const RAINBOW_MONO_DIFF = MONOSTAT_PER_LEVEL - RAINBOW_STAT_PER_LEVEL
const FULL_RAINBOW_PER_LEVEL = 6 * RAINBOW_STAT_PER_LEVEL
const LEGENDARY_CHLORELLA = 10
const LEGENDARY_CORDYCEPS = 10
const LEGENDARY_GINSENG = 6
const LEGENDARY_JUJUBES = 20
const GIRLS_PER_LEVEL_CAP = [0, 0, 0, 0, 0, 20, 25, 30, 35, 40, 50, 60, 70, 85, 100]

const boundMonostatCount = (count) => Math.max(MIN_POTENTIAL_MONOSTAT, Math.min(MAX_POTENTIAL_MONOSTAT, count))
const getClubBonus = (hasClub, multiplier = 1) => hasClub ? 1 + (0.1 * multiplier) : 1
const estimateUnboostedEnduranceForLevel = (level, monostatCount, hasClub, equipCaracs, opponentClass) => {
    const basePrimary = basePrimaryStatForLevel(level)
    const equipPrimary = equipCaracs ? equipCaracs[`carac${opponentClass}`] : equipPrimaryStatForLevel(level, monostatCount)
    const equipEndurance = equipCaracs ? equipCaracs.endurance : rainbowStatForLevel(level, 6 - monostatCount)
    const haremBonus = caculateHaremBonus(estimateHaremLevel(level))
    const clubBonus = getClubBonus(hasClub)
    const comboClubBonus = getClubBonus(hasClub, 2)

    return Math.round(ENDURANCE_PER_PRIMARY * basePrimary * comboClubBonus) +
        Math.round(ENDURANCE_PER_PRIMARY * equipPrimary * clubBonus) +
        equipEndurance * clubBonus +
        haremBonus * clubBonus
}
const basePrimaryStatForLevel = (level) => level * PRIMARY_PER_LEVEL
const equipPrimaryStatForLevel = (level, monostatCount) => rainbowStatForLevel(level, 6 - monostatCount) + monostatStatForLevel(level, monostatCount)
const rainbowStatForLevel = (level, count) => level * (count * RAINBOW_STAT_PER_LEVEL)
const monostatStatForLevel = (level, count) => level * (count * MONOSTAT_PER_LEVEL)
const estimateUnboostedPrimaryStatForLevel = (level, monostatCount, hasClub, equipCaracs, opponentClass) =>
    (basePrimaryStatForLevel(level) + (equipCaracs ? equipCaracs[`carac${opponentClass}`] : equipPrimaryStatForLevel(level, monostatCount))) * getClubBonus(hasClub)
const estimateHaremBonusForLevel = (level) => level * HAREM_BONUS_PER_LVL
const caculateHaremBonus = (haremLevel) => Math.round(Math.sqrt(haremLevel) * 50)
const calculateExtraPercent = (expected, actual) => Math.round(((actual - expected) / expected) * 100)
const buildResultTooltip = (existingContent, caracs, expected, actual, extraPercent) =>
    `${existingContent ? existingContent : ''}
<hr/>
<table>
<tr><td>Expected ${caracs.map(carac => `<span carac="${carac}"/>`).join('+')}:</td><td>${Math.round(expected).toLocaleString(locale)}</td></tr>
<tr><td>Actual ${caracs.map(carac => `<span carac="${carac}"/>`).join('+')}:</td><td>${Math.round(actual).toLocaleString(locale)}</td></tr>
</table>
${extraPercent > 0 ? `Extra: ${extraPercent}%` : ''}
`

function estimateHaremLevel(level) {
    const { opponent_fighter, loadedLeaguePlayers } = window
    let opponent_data
    if (Object.keys(loadedLeaguePlayers)?.length) {
        let opponentId = $('#leagues_right .avatar_border>img').attr('hero-page-id')
        opponent_data = loadedLeaguePlayers[opponentId].player
    } else {
        opponent_data = opponent_fighter.player
    }
    const teamLevels = opponent_data.team.girls.map(({ level }) => level)
    const teamLevel = teamLevels.reduce((a, b) => a + b, 0)
    const teamCount = teamLevels.length
    const girlsCount = opponent_data.team.synergies.map(({ harem_girls_count }) => harem_girls_count).reduce((a, b) => a + b, 0)

    if (girlsCount <= 7) {
        if (girlsCount == teamCount) {
            return teamLevel
        } else {
            return girlsCount * (teamLevel / teamCount)
        }
    } else {
        const levelCap = Math.ceil(Math.max(...teamLevels) / 50) * 50
        const min_girls = GIRLS_PER_LEVEL_CAP[levelCap / 50 - 1]

        if (levelCap <= 250 || (levelCap == 350 && girlsCount < min_girls)) {
            return girlsCount * (teamLevel / teamCount)
        } else {
            let bias = teamLevels.reduce((a, b) => a + (b - (levelCap - 50)), 0)
            return Math.min((min_girls * (levelCap - 50)) + (0.5 * level * girlsCount) + bias, levelCap * girlsCount)
        }
    }
}

function findBonusFromSynergies(synergies, element, teamGirlSynergyBonusesMissing, counts) {
    const { bonus_multiplier, team_bonus_per_girl } = synergies.find(({ element: { type } }) => type === element)

    return bonus_multiplier + (teamGirlSynergyBonusesMissing ? counts[element] * team_bonus_per_girl : 0)
}

const ELEMENTS = {
    egoDamage: {
        fire: 'nature',
        nature: 'stone',
        stone: 'sun',
        sun: 'water',
        water: 'fire'
    }
}
function calculateDominationBonuses(playerElements, opponentElements) {
    const bonuses = {
        opponent: {
            ego: 0,
            attack: 0,
        }
    };

    [
        { a: opponentElements, b: playerElements, k: 'opponent' }
    ].forEach(({ a, b, k }) => {
        a.forEach(element => {
            if (ELEMENTS.egoDamage[element] && b.includes(ELEMENTS.egoDamage[element])) {
                bonuses[k].ego += 0.1
                bonuses[k].attack += 0.1
            }
        })
    })

    return bonuses
}

async function getEquipDataFromProfile(playerId) {

    if (!profileDataCache[playerId]) {
        const html = await new Promise((res) => {
            window.$.ajax({
                url: `/hero/${playerId}/profile.html`,
                success: res
            })
        })

        const $page = $(html)

        const equip_code = $page.find('script').text()
        const equips = Object.values(JSON.parse(equip_code.match(/{.*}/)[0]))

        const stats = {}
        const CARAC_KEYS = ['1', '2', '3', 'endurance', 'chance']
        CARAC_KEYS.forEach(carac => {
            const caracVal = $page.find(`.fight_stats [carac=${carac}]`).text()
            stats[carac] = +caracVal.replace(/[^0-9]/g, '')
        })

        profileDataCache[playerId] = { equips, stats }
    }

    return profileDataCache[playerId]
}

if (currentPage.includes('tower-of-fame')) {
    boosterModule()
}

function boosterModule() {
    let opponent_data
    let opponentLvl
    let opponentEgo
    let opponentMainStat
    let opponentScndStat
    let opponentTertStat
    let opponentNonMainStatSum
    let opponentAtk
    let opponentDef
    let opponentEndurance
    let opponentHarmony
    let opponentClass
    let opponentMonostatCount
    let opponentHasClub
    let opponentGirlSum
    let opponentBonuses
    let isEstimate
    let $attack
    let $ego
    let $defense
    let $harmony
    let $attackMobile
    let $egoMobile
    let $defenseMobile
    let $harmonyMobile
    let ownDefenseReductionAdjustment = 0
    let attackDominanceBonusAdjustment = 0
    let egoDominanceBonusAdjustment = 0
    let attackResonanceBonusAdjustment = 0
    let egoResonanceBonusAdjustment = 0
    let harmonyResonanceBonusAdjustment = 0
    let equipCaracs

    async function getStats() {
        const { opponent_fighter, hero_fighter, loadedLeaguePlayers, GT } = window

        if (Object.keys(loadedLeaguePlayers)?.length) {
            let opponentId = $('#leagues_right .avatar_border>img').attr('hero-page-id')
            opponent_data = loadedLeaguePlayers[opponentId].player
        } else {
            opponent_data = opponent_fighter.player
        }
        opponentHasClub = !!(opponent_data.club && opponent_data.club.id_club)
        opponentLvl = parseInt(opponent_data.level, 10)
        opponentClass = opponent_data.class

        const { caracs } = opponent_data

        if (caracs) {
            opponentEgo = caracs.ego
            opponentMainStat = caracs[`carac${opponentClass}`]
            opponentScndStat = caracs[`carac${classRelationships[opponentClass].s}`]
            opponentTertStat = caracs[`carac${classRelationships[opponentClass].t}`]
            opponentEndurance = caracs.endurance
            opponentAtk = caracs.damage
            opponentHarmony = caracs.chance
            opponentDef = caracs.defense
        } else {
            opponentEgo = opponent_data.total_ego || opponent_data.remaining_ego
            opponentMainStat = opponent_data[`carac${opponentClass}`]
            opponentScndStat = opponent_data[`carac${classRelationships[opponentClass].s}`]
            opponentTertStat = opponent_data[`carac${classRelationships[opponentClass].t}`]
            opponentEndurance = opponent_data.endurance
            opponentAtk = opponent_data.damage
            opponentHarmony = opponent_data.chance
            opponentDef = opponent_data.defense
        }
        isEstimate = false

        const { equips, stats } = await getEquipDataFromProfile(opponent_data.id_fighter)

        const { team } = opponent_data
        const { synergies, total_power } = team
        opponentGirlSum = total_power

        const teamGirlSynergyBonusesMissing = synergies.every(({ team_girls_count }) => !team_girls_count)
        let counts
        if (teamGirlSynergyBonusesMissing) {
            console.log('Opponent Team Girl Synergy Bonuses Missing')
            const opponentTeamMemberElements = [];
            [0, 1, 2, 3, 4, 5, 6].forEach(key => {
                const teamMember = team.girls[key]
                if (teamMember && teamMember.element) {
                    opponentTeamMemberElements.push(teamMember.element)
                }
            })
            counts = opponentTeamMemberElements.reduce((a, b) => { a[b]++; return a }, {
                fire: 0,
                stone: 0,
                sun: 0,
                water: 0,
                nature: 0,
                darkness: 0,
                light: 0,
                psychic: 0
            })
        }
        opponentBonuses = {
            attack: findBonusFromSynergies(synergies, 'darkness', teamGirlSynergyBonusesMissing, counts),
            defense: findBonusFromSynergies(synergies, 'light', teamGirlSynergyBonusesMissing, counts),
            harmony: findBonusFromSynergies(synergies, 'psychic', teamGirlSynergyBonusesMissing, counts),
            ego: findBonusFromSynergies(synergies, 'nature', teamGirlSynergyBonusesMissing, counts),
        }
        ownDefenseReductionAdjustment = findBonusFromSynergies(hero_fighter.team.synergies, 'sun')

        const [heroTheme, opponentTheme] = [hero_fighter, opponent_data].map(data => data.team.theme_elements.map(({ type }) => type))
        const dominanceBonuses = calculateDominationBonuses(heroTheme, opponentTheme)

        const mythicEquipBonuses = {
            damage: 0,
            defense: 0,
            chance: 0,
            ego: 0,
        }
        equipCaracs = { carac1: 0, carac2: 0, carac3: 0, endurance: 0, chance: 0 }
        const CARAC_KEYS = ['carac1', 'carac2', 'carac3', 'endurance', 'chance']
        equips.forEach(equip => {
            if (equip.resonance_bonuses) {
                const { class: classBonus, theme } = equip.resonance_bonuses
                const matchesClass = `${classBonus.identifier}` === `${opponentClass}`
                if (matchesClass) {
                    mythicEquipBonuses[classBonus.resonance] += (+classBonus.bonus / 100)
                }

                const matchesTheme = (theme.identifier && opponentTheme.includes(theme.identifier)) || (!theme.identifier && !opponentTheme.length)
                if (matchesTheme) {
                    mythicEquipBonuses[theme.resonance] += (+theme.bonus / 100)
                }
            }
            CARAC_KEYS.forEach(caracKey => {
                equipCaracs[caracKey] += +equip[`${caracKey}_equip`]
            })
        })
        console.log('calculated mythic equip bonuses', mythicEquipBonuses)

        const rawHarmony = Math.ceil(stats.chance * (1 + opponentBonuses.harmony) * (1 + mythicEquipBonuses.chance))
        console.log('profile harm', rawHarmony, 'page harm', opponentHarmony, '(synergy:', opponentBonuses.harmony, '; equips:', mythicEquipBonuses.chance, '; total:', opponentHarmony, ')')
        const statsMatch = rawHarmony + 1 >= opponentHarmony && rawHarmony - 1 <= opponentHarmony
        console.log('stats match?', statsMatch)
        console.log('equip caracs', equipCaracs)

        if (statsMatch) {
            opponentMainStat = stats[opponentClass]
            opponentScndStat = stats[classRelationships[opponentClass].s]
            opponentTertStat = stats[classRelationships[opponentClass].t]
            opponentEndurance = stats.endurance
        }

        attackDominanceBonusAdjustment = dominanceBonuses.opponent.attack
        egoDominanceBonusAdjustment = dominanceBonuses.opponent.ego
        attackResonanceBonusAdjustment = mythicEquipBonuses.damage
        egoResonanceBonusAdjustment = mythicEquipBonuses.ego
        harmonyResonanceBonusAdjustment = mythicEquipBonuses.chance

        if (!opponentMainStat) {
            opponentMainStat = Math.ceil((((opponentAtk / (1 + attackDominanceBonusAdjustment)) / (1 + opponentBonuses.attack)) / (1 + mythicEquipBonuses.damage)) - (opponentGirlSum * 0.25))
            isEstimate = true
        }

        if (!opponentScndStat) {
            opponentNonMainStatSum = ((((opponentDef / (1 - ownDefenseReductionAdjustment)) / (1 + opponentBonuses.defense)) / (1 + mythicEquipBonuses.defense)) - (opponentGirlSum * 0.12)) * 4
            isEstimate = true
        } else {
            opponentNonMainStatSum = opponentScndStat + opponentTertStat
        }
        if (!opponentEndurance) {
            opponentEndurance = Math.ceil((((opponentEgo / 1 + egoDominanceBonusAdjustment) / (1 + opponentBonuses.ego)) / (1 + mythicEquipBonuses.ego)) - (opponentGirlSum * 2))
            isEstimate = true
        }

        if (!isEstimate) {
            const statRatio = opponentScndStat / opponentMainStat

            opponentMonostatCount = boundMonostatCount(Math.round(
                ((SECONDARY_PER_LEVEL + FULL_RAINBOW_PER_LEVEL) - ((PRIMARY_PER_LEVEL + FULL_RAINBOW_PER_LEVEL) * statRatio))
                /
                ((RAINBOW_MONO_DIFF * statRatio) + RAINBOW_STAT_PER_LEVEL)
            ))
        } else {
            const statRatio = opponentNonMainStatSum / opponentMainStat

            const monostatCountFromAttack = Math.round(
                ((TERTIARY_PER_LEVEL + SECONDARY_PER_LEVEL + (2 * FULL_RAINBOW_PER_LEVEL)) - ((PRIMARY_PER_LEVEL + FULL_RAINBOW_PER_LEVEL) * statRatio))
                /
                ((RAINBOW_MONO_DIFF * statRatio) + 2 * RAINBOW_STAT_PER_LEVEL)
            )
            const monostatCountFromHarmony = Math.round(
                MAX_POTENTIAL_MONOSTAT - (
                    ((opponentHarmony / (1 + opponentBonuses.harmony)) - opponentNonMainStatSum / 2)
                    /
                    ((RAINBOW_HARM_BASE + (opponentLvl * RAINBOW_HARM_PER_LEVEL)) * getClubBonus(opponentHasClub))
                )
            )

            opponentMonostatCount = boundMonostatCount(
                Math.min(monostatCountFromAttack, monostatCountFromHarmony)
            )
        }

        if (!opponentScndStat && isEstimate) {
            // Estimate sec and tert stats for display
            const secPerLevel = (SECONDARY_PER_LEVEL + (RAINBOW_STAT_PER_LEVEL * (6 - opponentMonostatCount)))
            const tertPerLevel = (TERTIARY_PER_LEVEL + (RAINBOW_STAT_PER_LEVEL * (6 - opponentMonostatCount)))
            const secShare = secPerLevel / (secPerLevel + tertPerLevel)
            const tertShare = tertPerLevel / (secPerLevel + tertPerLevel)

            opponentScndStat = Math.ceil(opponentNonMainStatSum * secShare)
            opponentTertStat = Math.ceil(opponentNonMainStatSum * tertShare)
        }

        $attack = $('#leagues_right .player_stats #player_attack_stat')
        $ego = $('#leagues_right .player_stats #player_ego_stat')
        $defense = $('#leagues_right .player_stats #player_defence_stat')
        $harmony = $('#leagues_right .player_stats #player_harmony_stat')
        $attackMobile = $('.selected-player-leagues .carac.attack')
        $egoMobile = $('.selected-player-leagues .carac.excitement') // [sic]
        $defenseMobile = $('.selected-player-leagues .carac.def0')
        $harmonyMobile = $('.selected-player-leagues .carac.harmony')

        const existingAttackTooltip = $attack.attr('tooltip')
        const existingDefenceTooltip = $defense.attr('tooltip')
        let existingEgoTooltip = $ego.attr('tooltip')
        let existingHarmonyTooltip = $harmony.attr('tooltip')
        if (existingEgoTooltip === '##carac_ego') {
            existingEgoTooltip = GT.ego
        }
        if (existingHarmonyTooltip === '!!HH_design:carac_chance!!') {
            existingHarmonyTooltip = GT.chance
        }

        const attackTooltip = `${existingAttackTooltip}<br/>
            ${isEstimate ? 'Estimate ' : ''}<span carac="class${opponentClass}"/> ${opponentMainStat.toLocaleString(locale)}<br/>
            Monostat count: ${opponentMonostatCount}`
        $attack.attr('tooltip', attackTooltip)
        $attackMobile.attr('tooltip', attackTooltip)

        const defenseTooltip = `${existingDefenceTooltip}<br/>
            ${isEstimate ? 'Estimate ' : ''}<span carac="class${classRelationships[opponentClass].s}"/> ${opponentScndStat.toLocaleString(locale)}<br/>
            ${isEstimate ? 'Estimate ' : ''}<span carac="class${classRelationships[opponentClass].t}"/> ${opponentTertStat.toLocaleString(locale)}`
        $defense.attr('tooltip', defenseTooltip)
        $defenseMobile.attr('tooltip', defenseTooltip)

        const egoTooltip = `${existingEgoTooltip}<br/>${isEstimate ? 'Estimate ' : ''}<span carac="endurance"/> ${opponentEndurance.toLocaleString(locale)}`
        $ego.attr('tooltip', egoTooltip)
        $egoMobile.attr('tooltip', egoTooltip)

        $harmony.attr('tooltip', existingHarmonyTooltip)
        $harmonyMobile.attr('tooltip', existingHarmonyTooltip)
    }

    function checkChlorella() {
        let expectedEgo

        if (!isEstimate) {
            expectedEgo = Math.ceil((opponentEndurance + (2 * opponentGirlSum)) * (1 + opponentBonuses.ego) * (1 + egoDominanceBonusAdjustment) * (1 + egoResonanceBonusAdjustment))
        } else {
            const expectedEndurance = estimateUnboostedEnduranceForLevel(opponentLvl, opponentMonostatCount, opponentHasClub, equipCaracs, opponentClass)
            expectedEgo = Math.ceil((expectedEndurance + (2 * opponentGirlSum)) * (1 + opponentBonuses.ego) * (1 + egoDominanceBonusAdjustment) * (1 + egoResonanceBonusAdjustment))
        }
        const extraPercent = calculateExtraPercent(expectedEgo, opponentEgo)

        if (LOGS_ENABLED) console.log(`CHLORELLA CHECK: Expected: ${expectedEgo}, Actual: ${opponentEgo}, Extra: ${extraPercent}%`);
        const existingTooltip = $ego.attr('tooltip')
        const newTooltip = buildResultTooltip(existingTooltip, ['ego'], expectedEgo, opponentEgo, extraPercent)
        $ego.attr('tooltip', newTooltip)
        $egoMobile.attr('tooltip', newTooltip)

        if (extraPercent > 0) {
            let boosted = 'boosted'
            if (extraPercent < 0.25 * LEGENDARY_CHLORELLA) {
                boosted = 'boosted_light'
            }
            $ego.addClass(boosted)
            $egoMobile.addClass(boosted)
        }
    }

    function checkCordyceps() {
        let expectedAttack
        if (!isEstimate) {
            const expectedUnrounded = opponentMainStat + (0.25 * opponentGirlSum)
            expectedAttack = Math.ceil(expectedUnrounded * (1 + opponentBonuses.attack) * (1 + attackDominanceBonusAdjustment) * (1 + attackResonanceBonusAdjustment))
        } else {
            const expectedMainStat = estimateUnboostedPrimaryStatForLevel(opponentLvl, opponentMonostatCount, opponentHasClub, equipCaracs, opponentClass)
            expectedAttack = Math.ceil((expectedMainStat + (0.25 * opponentGirlSum)) * (1 + opponentBonuses.attack) * (1 + attackDominanceBonusAdjustment) * (1 + attackResonanceBonusAdjustment))
        }
        const extraPercent = calculateExtraPercent(expectedAttack, opponentAtk)

        if (LOGS_ENABLED) console.log(`CORDYCEPS CHECK: Expected: ${expectedAttack}, Actual: ${opponentAtk}, Extra: ${extraPercent}%`);
        const existingTooltip = $attack.attr('tooltip')
        const newTooltip = buildResultTooltip(existingTooltip, ['damage'], expectedAttack, opponentAtk, extraPercent)
        $attack.attr('tooltip', newTooltip)
        $attackMobile.attr('tooltip', newTooltip)

        if (extraPercent > 0) {
            let boosted = 'boosted'
            if (extraPercent < 0.25 * LEGENDARY_CORDYCEPS) {
                boosted = 'boosted_light'
            }
            $attack.addClass(boosted)
            $attackMobile.addClass(boosted)
        }
    }

    function checkGinseng() {
        let expectedMainStat
        let expectedNonMainStatSum
        let extraPercent
        if (!isEstimate) {
            expectedMainStat = estimateUnboostedPrimaryStatForLevel(opponentLvl, opponentMonostatCount, opponentHasClub, equipCaracs, opponentClass)
            extraPercent = calculateExtraPercent(expectedMainStat, opponentMainStat)
        } else {
            expectedNonMainStatSum = (opponentLvl * (SECONDARY_PER_LEVEL + TERTIARY_PER_LEVEL)) + equipCaracs[`carac${classRelationships[opponentClass].s}`] + equipCaracs[`carac${classRelationships[opponentClass].t}`]
            extraPercent = Math.round(
                ((opponentNonMainStatSum / expectedNonMainStatSum) - getClubBonus(opponentHasClub)) * 100
            )
        }

        if (LOGS_ENABLED) console.log(`GINSENG CHECK: Expected: ${isEstimate ? expectedNonMainStatSum : expectedMainStat}, Actual: ${isEstimate ? opponentNonMainStatSum : opponentMainStat}, Extra: ${extraPercent}%, Monostat count: ${opponentMonostatCount}, Has club: ${opponentHasClub}`);
        const existingTooltip = $defense.attr('tooltip')
        const newTooltip = buildResultTooltip(
            existingTooltip,
            isEstimate ? [`class${classRelationships[opponentClass].s}`, `class${classRelationships[opponentClass].t}`] : [`class${opponentClass}`],
            isEstimate ? expectedNonMainStatSum * getClubBonus(opponentHasClub) : expectedMainStat,
            isEstimate ? opponentNonMainStatSum : opponentMainStat,
            extraPercent)
        $defense.attr('tooltip', newTooltip)
        $defenseMobile.attr('tooltip', newTooltip)

        if (extraPercent > 0) {
            let boosted = 'boosted'
            if (extraPercent < 0.25 * LEGENDARY_GINSENG) {
                boosted = 'boosted_light'
            }
            $defense.addClass(boosted)
            $defenseMobile.addClass(boosted)
        }
    }

    function checkJujubes() {
        const clubBonus = getClubBonus(opponentHasClub)

        const expectedUnrounded = ((opponentNonMainStatSum * 0.5 * clubBonus) + equipCaracs.chance) * (1 + opponentBonuses.harmony) * (1 + harmonyResonanceBonusAdjustment)
        const expectedHarmony = Math.ceil(expectedUnrounded)
        const extraPercent = calculateExtraPercent(expectedHarmony, opponentHarmony)

        if (LOGS_ENABLED) console.log(`JUJUBES CHECK: Expected: ${expectedHarmony}, Actual: ${opponentHarmony}, Extra: ${extraPercent}%, Monostat count: ${opponentMonostatCount}, Has club: ${opponentHasClub}`);
        const existingTooltip = $harmony.attr('tooltip')
        const newTooltip = buildResultTooltip(existingTooltip, ['chance'], expectedHarmony, opponentHarmony, extraPercent)
        $harmony.attr('tooltip', newTooltip)
        $harmonyMobile.attr('tooltip', newTooltip)

        if (extraPercent > 0) {
            let boosted = 'boosted'
            if (extraPercent < 0.25 * LEGENDARY_JUJUBES) {
                boosted = 'boosted_light'
            }
            $harmony.addClass(boosted)
            $harmonyMobile.addClass(boosted)
        }
    }

    async function checkBoosters() {
        const $statsContainer = $('#leagues_right .player_stats')
        $statsContainer.addClass('booster-detector-pending')
        await getStats()

        checkCordyceps()
        checkChlorella()
        checkGinseng()
        checkJujubes()
        $statsContainer.removeClass('booster-detector-pending')
    }

    // Observer grabbed from HH++
    let opntName;
    $('.leadTable').click(function () {
        opntName = ''
    })
    function waitOpnt() {
        setTimeout(function () {
            if ($('#leagues_right .team-member > img').eq(3).data('new-girl-tooltip')) {
                checkBoosters()
            }
            else {
                waitOpnt()
            }
        }, 50);
    }
    const observeCallback = function () {
        const opntNameNew = $('#leagues_right .leagues_team_block .title')[0].innerHTML
        if (opntName !== opntNameNew) {
            opntName = opntNameNew
            waitOpnt()
        }
    }
    const observer = new MutationObserver(observeCallback);
    const test = document.getElementById('leagues_right');
    observer.observe(test, { attributes: false, childList: true, subtree: false });

    sheet.insertRule(`
    #leagues_right .boosted, .selected-player-leagues .boosted {
        color: #FF2F2F;
        text-shadow: rgb(0, 0, 0) 1px 1px 0px, rgb(0, 0, 0) -1px 1px 0px, rgb(0, 0, 0) -1px -1px 0px, rgb(0, 0, 0) 1px -1px 0px;
    }
    `);
    sheet.insertRule(`
    #leagues_right .boosted_light, .selected-player-leagues .boosted_light {
        color: #FFA500;
        text-shadow: rgb(0, 0, 0) 1px 1px 0px, rgb(0, 0, 0) -1px 1px 0px, rgb(0, 0, 0) -1px -1px 0px, rgb(0, 0, 0) 1px -1px 0px;
    }
    `);
    sheet.insertRule(`
    .booster-detector-pending {
        color: #aaa;
    }
    `);
}
