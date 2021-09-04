// ==UserScript==
// @name            Hentai Heroes++ League Booster Detector Add-on
// @description     Adding detection of boosters to league.
// @version         0.1.0
// @match           https://www.hentaiheroes.com/*
// @match           https://nutaku.haremheroes.com/*
// @match           https://eroges.hentaiheroes.com/*
// @match           https://thrix.hentaiheroes.com/*
// @match           https://test.hentaiheroes.com/*
// @run-at          document-end
// @updateURL       https://raw.githubusercontent.com/45026831/hh-booster-detector/main/hh-booster-detector.js
// @downloadURL     https://raw.githubusercontent.com/45026831/hh-booster-detector/main/hh-booster-detector.js
// @grant           none
// @author          45026831(Numbers), zoopokemon
// ==/UserScript==

/*  ===========
     CHANGELOG
    =========== */
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
const {$, location} = window;
const LOGS_ENABLED = false

if (!$) {
    console.log('HH++ BOOSTER DETECTOR WARNING: No jQuery found. Probably an error page. Ending the script here');
    return;
}

// Define CSS
const sheet = (function() {
    const style = document.createElement('style')
    document.head.appendChild(style)
    return style.sheet
})()

const currentPage = location.pathname

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

const lang = $('html')[0].lang.substring(0,2)
let locale = 'fr'
if (lang === 'en') {
    locale = 'en'
}

// Magic numbers
const RAINBOW_STAT_PER_LEVEL = 7.2
const RAINBOW_HARM_PER_LEVEL = 9.1
const RAINBOW_HARM_BASE      = 90
const MONOSTAT_PER_LEVEL     = 11.15
const PRIMARY_PER_LEVEL      = 9+30
const SECONDARY_PER_LEVEL    = 7+30
const TERTIARY_PER_LEVEL     = 5+30
const ENDURANCE_PER_PRIMARY  = 4
const DEFENCE_PER_NON_PRIM   = 0.25
const HARMONY_PER_NON_PRIM   = 0.5
const MIN_POTENTIAL_MONOSTAT = 0
const MAX_POTENTIAL_MONOSTAT = 6
const HAREM_BONUS_PER_LVL    = 52
const RAINBOW_MONO_DIFF      = MONOSTAT_PER_LEVEL - RAINBOW_STAT_PER_LEVEL
const FULL_RAINBOW_PER_LEVEL = 6 * RAINBOW_STAT_PER_LEVEL
const LEGENDARY_CHLORELLA    = 10
const LEGENDARY_CORDYCEPS    = 10
const LEGENDARY_GINSENG      = 6
const LEGENDARY_JUJUBES      = 20

const boundMonostatCount = (count) => Math.max(MIN_POTENTIAL_MONOSTAT, Math.min(MAX_POTENTIAL_MONOSTAT, count))
const getClubBonus = (hasClub, multiplier = 1) => hasClub ? 1 + (0.1*multiplier) : 1
const estimateUnboostedEnduranceForLevel = (level, monostatCount, hasClub) => {
    const basePrimary = basePrimaryStatForLevel(level)
    const equipPrimary = equipPrimaryStatForLevel(level, monostatCount)
    const equipEndurance = rainbowStatForLevel(level, 6-monostatCount)
    const haremBonus = estimateHaremBonusForLevel(level)
    const clubBonus = getClubBonus(hasClub)
    const comboClubBonus = getClubBonus(hasClub, 2)

    return Math.round(ENDURANCE_PER_PRIMARY * basePrimary * comboClubBonus) +
        Math.round(ENDURANCE_PER_PRIMARY * equipPrimary * clubBonus) +
        equipEndurance * clubBonus +
        haremBonus
}
const basePrimaryStatForLevel = (level) => level * PRIMARY_PER_LEVEL
const equipPrimaryStatForLevel = (level, monostatCount) => rainbowStatForLevel(level, 6-monostatCount) + monostatStatForLevel(level, monostatCount)
const rainbowStatForLevel = (level, count) => level * (count*RAINBOW_STAT_PER_LEVEL)
const monostatStatForLevel = (level, count) => level * (count*MONOSTAT_PER_LEVEL)
const estimateUnboostedPrimaryStatForLevel = (level, monostatCount, hasClub) =>
    (basePrimaryStatForLevel(level) + equipPrimaryStatForLevel(level, monostatCount)) * getClubBonus(hasClub)
const estimateHaremBonusForLevel = (level) => level * HAREM_BONUS_PER_LVL
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

if (currentPage.includes('tower-of-fame')) {
    boosterModule()
}

function boosterModule () {
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
    let isEstimate
    let $attack
    let $ego
    let $defense
    let $harmony

    function getStats() {
        const {playerLeaguesData} = window

        opponentHasClub = !!playerLeaguesData.club.id_club
        opponentLvl = parseInt(playerLeaguesData.level, 10)
        opponentClass = playerLeaguesData.class

        const {caracs} = playerLeaguesData

        opponentEgo = caracs.ego
        opponentMainStat = caracs[`carac${opponentClass}`]
        opponentScndStat = caracs[`carac${classRelationships[opponentClass].s}`]
        opponentTertStat = caracs[`carac${classRelationships[opponentClass].t}`]
        opponentEndurance = caracs.endurance
        opponentAtk = caracs.damage
        opponentHarmony = caracs.chance
        opponentDef = caracs.defense
        isEstimate = false

        opponentGirlSum = playerLeaguesData.team.map(({caracs}) => Object.values(caracs).reduce((s,c) => s+c, 0)).reduce((s,c) => s+c, 0)

        if (!opponentMainStat) {
            opponentMainStat = Math.ceil(opponentAtk - (opponentGirlSum * 0.25))
            isEstimate = true
        }

        if (!opponentScndStat) {
            opponentNonMainStatSum = (opponentDef - (opponentGirlSum * 0.12)) * 4
            isEstimate = true
        } else {
            opponentNonMainStatSum = opponentScndStat + opponentTertStat
        }
        if (!opponentEndurance) {
            opponentEndurance = Math.ceil(opponentEgo - (opponentGirlSum * 2))
            isEstimate = true
        }

        if (!isEstimate) {
            const statRatio = opponentScndStat / opponentMainStat

            opponentMonostatCount = boundMonostatCount(Math.round(
                ((SECONDARY_PER_LEVEL+FULL_RAINBOW_PER_LEVEL) - ((PRIMARY_PER_LEVEL+FULL_RAINBOW_PER_LEVEL) * statRatio))
                /
                ((RAINBOW_MONO_DIFF * statRatio) + RAINBOW_STAT_PER_LEVEL)
                ))
        } else {
            const statRatio = opponentNonMainStatSum / opponentMainStat

            const monostatCountFromAttack = Math.round(
                ((TERTIARY_PER_LEVEL + SECONDARY_PER_LEVEL + (2*FULL_RAINBOW_PER_LEVEL))-((PRIMARY_PER_LEVEL+FULL_RAINBOW_PER_LEVEL) * statRatio))
                /
                ((RAINBOW_MONO_DIFF * statRatio) + 2*RAINBOW_STAT_PER_LEVEL)
                )
            const monostatCountFromHarmony = Math.round(
                MAX_POTENTIAL_MONOSTAT - (
                    (opponentHarmony - opponentNonMainStatSum/2)
                    /
                    ((RAINBOW_HARM_BASE + (opponentLvl * RAINBOW_HARM_PER_LEVEL)) * getClubBonus(opponentHasClub))
                )
            )

            opponentMonostatCount = boundMonostatCount(
                Math.min(monostatCountFromAttack, monostatCountFromHarmony)
            )
        }

        if(!opponentScndStat && isEstimate) {
            // Estimate sec and tert stats for display
            const secPerLevel = (SECONDARY_PER_LEVEL+(RAINBOW_STAT_PER_LEVEL*(6-opponentMonostatCount)))
            const tertPerLevel = (TERTIARY_PER_LEVEL+(RAINBOW_STAT_PER_LEVEL*(6-opponentMonostatCount)))
            const secShare = secPerLevel / (secPerLevel + tertPerLevel)
            const tertShare = tertPerLevel / (secPerLevel + tertPerLevel)

            opponentScndStat = Math.ceil(opponentNonMainStatSum * secShare)
            opponentTertStat = Math.ceil(opponentNonMainStatSum * tertShare)
        }

        $attack = $('#leagues_right .stats_wrap .stat:nth-of-type(1)')
        $ego = $('#leagues_right .stats_wrap .stat:nth-of-type(2)')
        $defense = $('#leagues_right .stats_wrap .stat:nth-of-type(3)')
        $harmony = $('#leagues_right .stats_wrap .stat:nth-of-type(4)')

        const existingAttackTooltip = $attack.attr('hh_title')
        const existingDefenceTooltip = $defense.attr('hh_title')
        let existingEgoTooltip = $ego.attr('hh_title')
        let existingHarmonyTooltip = $harmony.attr('hh_title')
        if (existingEgoTooltip === '##carac_ego') {
            existingEgoTooltip = GT.ego
        }
        if (existingHarmonyTooltip === '!!HH_design:carac_chance!!') {
            existingHarmonyTooltip = GT.chance
        }

        $attack.attr('hh_title',
            `${existingAttackTooltip}<br/>
            ${isEstimate ? 'Estimate ':''}<span carac="class${opponentClass}"/> ${opponentMainStat.toLocaleString(locale)}<br/>
            Monostat count: ${opponentMonostatCount}`)
        $defense.attr('hh_title',
            `${existingDefenceTooltip}<br/>
            ${isEstimate ? 'Estimate ':''}<span carac="class${classRelationships[opponentClass].s}"/> ${opponentScndStat.toLocaleString(locale)}<br/>
            ${isEstimate ? 'Estimate ':''}<span carac="class${classRelationships[opponentClass].t}"/> ${opponentTertStat.toLocaleString(locale)}`)
        $ego.attr('hh_title', `${existingEgoTooltip}<br/>${isEstimate ? 'Estimate ':''}<span carac="endurance"/> ${opponentEndurance.toLocaleString(locale)}`)
        $harmony.attr('hh_title', existingHarmonyTooltip)
    }

    function checkChlorella () {
        let expectedEgo

        if (!isEstimate) {
            expectedEgo = opponentEndurance + (2 * opponentGirlSum)
        } else {
            const expectedEndurance = estimateUnboostedEnduranceForLevel(opponentLvl, opponentMonostatCount, opponentHasClub)
            expectedEgo = expectedEndurance + (2 * opponentGirlSum)
        }
        const extraPercent = calculateExtraPercent(expectedEgo, opponentEgo)

        if(LOGS_ENABLED) console.log(`CHLORELLA CHECK: Expected: ${expectedEgo}, Actual: ${opponentEgo}, Extra: ${extraPercent}%`);
        const existingTooltip = $ego.attr('hh_title')
        const newTooltip = buildResultTooltip(existingTooltip, ['ego'], expectedEgo, opponentEgo, extraPercent)
        $ego.attr('hh_title', newTooltip)

        if (extraPercent > 0) {
            let boosted = 'boosted'
            if (extraPercent < 0.25 * LEGENDARY_CHLORELLA) {
                boosted = 'boosted_light'
            }
            $ego.addClass(boosted)
            addIcon('chlor')
        }
    }

    function checkCordyceps () {
        let expectedAttack
        if (!isEstimate) {
            const expectedUnrounded = opponentMainStat + (0.25 * opponentGirlSum)
            expectedAttack = Math.ceil(expectedUnrounded)
        } else {
            const expectedMainStat = estimateUnboostedPrimaryStatForLevel(opponentLvl, opponentMonostatCount, opponentHasClub)
            expectedAttack = expectedMainStat + (0.25 * opponentGirlSum)
        }
        const extraPercent = calculateExtraPercent(expectedAttack, opponentAtk)

        if(LOGS_ENABLED) console.log(`CORDYCEPS CHECK: Expected: ${expectedAttack}, Actual: ${opponentAtk}, Extra: ${extraPercent}%`);
        const existingTooltip = $attack.attr('hh_title')
        const newTooltip = buildResultTooltip(existingTooltip, ['damage'], expectedAttack, opponentAtk, extraPercent)
        $attack.attr('hh_title', newTooltip)

        if (extraPercent > 0) {
            let boosted = 'boosted'
            if (extraPercent < 0.25 * LEGENDARY_CORDYCEPS) {
                boosted = 'boosted_light'
            }
            $('#leagues_right div.fighter-stats-container > div:nth-child(1)').addClass(boosted)
            addIcon('cordy')
        }
    }

    function checkGinseng () {
        let expectedMainStat
        let expectedNonMainStatSum
        let extraPercent
        if (!isEstimate) {
            expectedMainStat = estimateUnboostedPrimaryStatForLevel(opponentLvl, opponentMonostatCount, opponentHasClub)
            extraPercent = calculateExtraPercent(expectedMainStat, opponentMainStat)
        } else {
            expectedNonMainStatSum = opponentLvl * (SECONDARY_PER_LEVEL + TERTIARY_PER_LEVEL + 2*RAINBOW_STAT_PER_LEVEL*(6-opponentMonostatCount))
            extraPercent = Math.round(
                ((opponentNonMainStatSum / expectedNonMainStatSum) - getClubBonus(opponentHasClub)) * 100
            )
        }

        if(LOGS_ENABLED) console.log(`GINSENG CHECK: Expected: ${isEstimate ? expectedNonMainStatSum : expectedMainStat}, Actual: ${isEstimate ? opponentNonMainStatSum : opponentMainStat}, Extra: ${extraPercent}%, Monostat count: ${opponentMonostatCount}, Has club: ${opponentHasClub}`);
        const existingTooltip = $defense.attr('hh_title')
        const newTooltip = buildResultTooltip(
            existingTooltip, 
            isEstimate ? [`class${classRelationships[opponentClass].s}`, `class${classRelationships[opponentClass].t}`] : [`class${opponentClass}`],
            isEstimate ? expectedNonMainStatSum * getClubBonus(opponentHasClub) : expectedMainStat,
            isEstimate ? opponentNonMainStatSum : opponentMainStat,
            extraPercent)
        $defense.attr('hh_title', newTooltip)

        if (extraPercent > 0) {
            let boosted = 'boosted'
            if (extraPercent < 0.25 * LEGENDARY_GINSENG) {
                boosted = 'boosted_light'
            }
            $('#leagues_right div.fighter-stats-container > div:nth-child(3)').addClass(boosted)
            addIcon('ginseng')
        }
    }

    function checkJujubes () {
        const clubBonus = getClubBonus(opponentHasClub)

        const expectedUnrounded = ((opponentNonMainStatSum) * 0.5 * clubBonus) + ((6 - opponentMonostatCount) * Math.ceil(RAINBOW_HARM_BASE + (opponentLvl * RAINBOW_HARM_PER_LEVEL)))
        const expectedHarmony = Math.ceil(expectedUnrounded)
        const extraPercent = calculateExtraPercent(expectedHarmony, opponentHarmony)

        if(LOGS_ENABLED) console.log(`JUJUBES CHECK: Expected: ${expectedHarmony}, Actual: ${opponentHarmony}, Extra: ${extraPercent}%, Monostat count: ${opponentMonostatCount}, Has club: ${opponentHasClub}`);
        const existingTooltip = $harmony.attr('hh_title')
        const newTooltip = buildResultTooltip(existingTooltip, ['chance'], expectedHarmony, opponentHarmony, extraPercent)
        $harmony.attr('hh_title', newTooltip)

        if (extraPercent > 0) {
            let boosted = 'boosted'
            if (extraPercent < 0.25 * LEGENDARY_JUJUBES) {
                boosted = 'boosted_light'
            }
            $('#leagues_right div.fighter-stats-container > div:nth-child(4)').addClass(boosted)
            addIcon('jujubes')
        }
    }

    function setupIconHolder () {
        let iconHolder = $('.leadTable .lead_table_default .booster_icons')

        if (!iconHolder.length) {
            iconHolder = $('<span class="booster_icons"></span>')
            $('.leadTable .lead_table_default .nickname').append(iconHolder)
        }

        iconHolder.empty()
    }

    function addIcon (type) {
        if(!isEstimate) {
            $('.leadTable .lead_table_default .booster_icons').append(`<span class="booster_icon boosted_${type}"></span>`)
        }
    }

    function checkBoosters () {
        setupIconHolder()
        getStats()

        checkCordyceps()
        checkChlorella()
        checkGinseng()
        checkJujubes()
    }
    checkBoosters()

    // Observer grabbed from HH++
    let opntName;
    $('.leadTable').click(function() {
        opntName=''
    })
    function waitOpnt() {
        setTimeout(function() {
            if ($('#leagues_right .team-member > img').data('new-girl-tooltip')) {
                checkBoosters();
            }
            else {
                waitOpnt()
            }
        }, 50);
    }
    const observeCallback = function() {
        const opntNameNew = $('#leagues_right .player_block .title')[0].innerHTML
        if (opntName !== opntNameNew) {
            opntName = opntNameNew;
            waitOpnt();
        }
    }
    const observer = new MutationObserver(observeCallback);
    const test = document.getElementById('leagues_right');
    observer.observe(test, {attributes: false, childList: true, subtree: false});

    sheet.insertRule(`
    #leagues_right .boosted {
        color: #FF2F2F;
    }
    `);
    sheet.insertRule(`
    #leagues_right .boosted_light {
        color: #FFA500;
    }
    `);
    sheet.insertRule(`
    .leadTable .booster_icons {
        display: inline-flex;
        flex: 1;
        margin: 0 !important;
        align-items: center;
        justify-content: flex-end;
    }
    `);
    sheet.insertRule(`
    .leadTable .booster_icon {
        background-size: contain;
        background-position-y: center;
        background-repeat: no-repeat;
        height: 20px;
        max-width: 20px;
        flex: 1;
        margin: 0 !important;
    }
    `);

    const icons = {
        ginseng: 'https://hh.hh-content.com/pictures/items/B1.png',
        jujubes: 'https://hh.hh-content.com/pictures/items/B2.png',
        chlor: 'https://hh.hh-content.com/pictures/items/B3.png',
        cordy: 'https://hh.hh-content.com/pictures/items/B4.png'
    }

    Object.keys(icons).forEach(booster => {
        sheet.insertRule(`
        .leadTable .boosted_${booster} {
            background: url('${icons[booster]}');
        }
        `)
    })

    sheet.insertRule(`
    .lead_table table tbody tr>td .nickname {
        display: inline-flex;
        align-items: center;
        justify-content: space-between;
    }
    `);
}
