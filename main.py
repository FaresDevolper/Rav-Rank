import os
import io
import math
import time
import random
import asyncio
import datetime
from collections import defaultdict
from itertools import combinations

import discord
from discord import app_commands
from discord.ext import commands, tasks
from aiohttp import web
from motor.motor_asyncio import AsyncIOMotorClient
from pymongo import UpdateOne
from PIL import Image, ImageDraw, ImageFont, ImageFilter, ImageOps


# ============================================================
# الاعدادات الاساسية
# ============================================================

TOKEN = os.getenv("TOKEN") or os.getenv("DISCORD_TOKEN")
MONGO_URI = os.getenv("MONGO_URI") or os.getenv("MONGO_URL")

# اياردي السيرفر
GUILD_ID = 1425195739591610451

# الروم اللي تجي فيه رسائل الترقية والاحداث
ANNOUNCE_CHANNEL_ID = 1558776261814386708

# رولات المستويات بالشكل التالي المستوى ثم اياردي الرول
# مثال: LEVEL_ROLES = {5: 111111111111111111}
LEVEL_ROLES = {}

# رومات او رولات ما تعطي اكسبي
IGNORED_CHANNEL_IDS = []
IGNORED_ROLE_IDS = []

# حالة البوت البنفسجية ستريمنج
STREAM_NAME = "Rav Pulse"
STREAM_URL = "https://www.twitch.tv/ravserver"

# ------------------------------------------------------------
# اكسبي الشات والصوت
# ------------------------------------------------------------
CHAT_COOLDOWN = 25
CHAT_XP_MIN = 8
CHAT_XP_MAX = 14
CONVO_XP_SENDER = 4
CONVO_XP_TARGET = 8
VOICE_XP_PER_MIN = 10
VOICE_CAM_BONUS = 1.25
CROWD_STEP = 0.15
CROWD_MAX = 2.0
DAILY_CHAT_CAP = 4000
DAILY_VOICE_CAP = 8000
PRESTIGE_LEVEL = 50

# ------------------------------------------------------------
# نبض السيرفر
# ------------------------------------------------------------
PULSE_GOAL = 15000
PULSE_BOOST_MINUTES = 60
PULSE_BOOST_MULT = 2.0

# ------------------------------------------------------------
# الروابط بين الاعضاء
# ------------------------------------------------------------
BOND_CHAT_POINTS = 3
BOND_VOICE_POINTS = 1
BOND_DIVISOR = 15
BOND_MAX_ROOM = 12
BOND_ANNOUNCE_LIMIT = 3

# ------------------------------------------------------------
# المهام اليومية
# ------------------------------------------------------------
QUEST_ANNOUNCE = True
TZ_OFFSET_HOURS = 3

QUEST_POOL = [
    {"id": "chat", "text": "أرسل {t} رسالة في الشات", "target": 30, "reward": 150},
    {"id": "voice", "text": "اقضِ {t} دقيقة في الرومات الصوتية", "target": 30, "reward": 220},
    {"id": "people", "text": "تفاعل مع {t} أشخاص مختلفين في الشات", "target": 3, "reward": 180},
    {"id": "replies", "text": "احصل على {t} ردود من الأعضاء على رسائلك", "target": 5, "reward": 200},
    {"id": "partners", "text": "اجلس في الصوت مع {t} أشخاص مختلفين", "target": 3, "reward": 200},
]

# ------------------------------------------------------------
# المظهر
# ------------------------------------------------------------
BEIGE = 0xD8C3A5
BACKGROUND_PATH = "leaderboard.png"

# سبب الترقية الذي يظهر في بطاقة الترقية حسب مصدر الاكسبي
LEVEL_REASONS = {
    "chat": "Chat activity",
    "voice": "Voice activity",
    "other": "Presence in the server",
    "admin": "Staff adjustment",
}

# الوان بطاقة الترقية
CARD_WIDTH = 1000
CARD_HEIGHT = 380
CARD_DEEP = (20, 14, 8)
CARD_ACCENT = (216, 195, 165)
CARD_SOFT = (240, 228, 208)
CARD_MUTED = (170, 155, 130)


# ============================================================
# الحالة والذاكرة المؤقتة
# ============================================================

STATE = {
    "pulse": 0,
    "boost_until": 0.0,
    "admin_mult": 1.0,
    "admin_mult_until": 0.0,
    "ignored": [],
}

DEFAULT_USER = {
    "xp": 0,
    "level": 0,
    "prestige": 0,
    "msgs": 0,
    "voice_min": 0,
    "day": "",
    "d_chat": 0,
    "d_voice": 0,
}

mongo = None
users = None
bonds_col = None
quests_col = None
meta = None

user_locks = defaultdict(asyncio.Lock)
last_msg = {}
last_xp = {}
pair_cd = {}
xp_cmd_cd = {}
bond_points = {}
bond_dirty = set()
quest_cache = {}
quest_set_cache = {}
LAST_DAY = {"value": ""}

if not TOKEN:
    raise SystemExit("TOKEN غير موجود في متغيرات البيئة")
if not MONGO_URI:
    raise SystemExit("MONGO_URI غير موجود في متغيرات البيئة")


# ============================================================
# دوال مساعدة
# ============================================================

def today_str():
    now = datetime.datetime.now(datetime.timezone.utc) + datetime.timedelta(hours=TZ_OFFSET_HOURS)
    return now.strftime("%Y-%m-%d")


def xp_for_level(level):
    return 5 * (level ** 2) + 50 * level + 100


def level_from_xp(total):
    level = 0
    remaining = total
    while remaining >= xp_for_level(level):
        remaining -= xp_for_level(level)
        level += 1
    return level, remaining, xp_for_level(level)


def make_bar(current, total, size=12):
    if total <= 0:
        return "░" * size
    filled = int(size * min(current, total) / total)
    return "█" * filled + "░" * (size - filled)


def get_guild():
    if GUILD_ID:
        return bot.get_guild(GUILD_ID)
    return bot.guilds[0] if bot.guilds else None


def has_ignored_role(member):
    return any(r.id in IGNORED_ROLE_IDS for r in member.roles)


def is_ignored_channel(channel_id):
    return channel_id in IGNORED_CHANNEL_IDS or channel_id in STATE["ignored"]


def current_mult():
    now = time.time()
    mult = 1.0
    if now < STATE["boost_until"]:
        mult *= PULSE_BOOST_MULT
    if now < STATE["admin_mult_until"]:
        mult *= STATE["admin_mult"]
    return mult


async def load_user(uid):
    doc = await users.find_one({"_id": uid})
    if doc is None:
        doc = {"_id": uid}
        doc.update(DEFAULT_USER)
    else:
        for key, value in DEFAULT_USER.items():
            doc.setdefault(key, value)
    return doc


# ============================================================
# الاعلانات والرولات
# ============================================================

async def get_announce_channel():
    channel = bot.get_channel(ANNOUNCE_CHANNEL_ID)
    if channel is None:
        try:
            channel = await bot.fetch_channel(ANNOUNCE_CHANNEL_ID)
        except Exception:
            return None
    return channel


async def send_announce(content=None, embed=None, allowed=None):
    channel = await get_announce_channel()
    if channel is None:
        return
    if allowed is None:
        allowed = discord.AllowedMentions(users=True)
    try:
        await channel.send(content=content, embed=embed, allowed_mentions=allowed)
    except Exception as e:
        print(f"announce error {e}")


async def sync_level_roles(member, level):
    if not LEVEL_ROLES:
        return
    eligible = [lv for lv in LEVEL_ROLES if lv <= level]
    target_id = LEVEL_ROLES[max(eligible)] if eligible else None
    try:
        for rid in LEVEL_ROLES.values():
            if rid == target_id:
                continue
            role = member.guild.get_role(rid)
            if role and role in member.roles:
                await member.remove_roles(role, reason="Rav Pulse")
        if target_id:
            role = member.guild.get_role(target_id)
            if role and role not in member.roles:
                await member.add_roles(role, reason="Rav Pulse")
    except discord.HTTPException as e:
        print(f"roles error {e}")


async def on_level_up(member, old, new, reason="other"):
    await sync_level_roles(member, new)
    await send_levelup_card(member, old, new, reason)


# ============================================================
# محرك الاكسبي
# ============================================================

async def add_pulse(amount):
    STATE["pulse"] += amount
    now = time.time()
    if STATE["pulse"] >= PULSE_GOAL:
        if now >= STATE["boost_until"]:
            STATE["pulse"] = 0
            STATE["boost_until"] = now + PULSE_BOOST_MINUTES * 60
            embed = discord.Embed(
                title="نبض السيرفر وصل للهدف",
                description=f"بفضل نشاطكم صار كل اكسبي مضاعف لمدة {PULSE_BOOST_MINUTES} دقيقة",
                color=BEIGE,
            )
            await send_announce(embed=embed)
        else:
            STATE["pulse"] = PULSE_GOAL


async def award_xp(member, amount, source, extra=1.0, use_mult=True, add_msgs=0, add_voice=0):
    if amount <= 0 or member.bot:
        return 0
    mult = current_mult() if use_mult else 1.0
    amount = max(1, int(round(amount * mult * extra)))
    today = today_str()
    async with user_locks[member.id]:
        doc = await load_user(member.id)
        if doc["day"] != today:
            doc["day"] = today
            doc["d_chat"] = 0
            doc["d_voice"] = 0
        if source == "chat":
            room = DAILY_CHAT_CAP - doc["d_chat"]
            if room <= 0:
                return 0
            amount = min(amount, room)
            doc["d_chat"] += amount
        elif source == "voice":
            room = DAILY_VOICE_CAP - doc["d_voice"]
            if room <= 0:
                return 0
            amount = min(amount, room)
            doc["d_voice"] += amount
        old_level = doc["level"]
        doc["xp"] += amount
        doc["msgs"] += add_msgs
        doc["voice_min"] += add_voice
        new_level = level_from_xp(doc["xp"])[0]
        doc["level"] = new_level
        await users.replace_one({"_id": member.id}, doc, upsert=True)
    await add_pulse(amount)
    if new_level > old_level:
        await on_level_up(member, old_level, new_level, source)
    return amount


async def change_xp(member, mode, value):
    async with user_locks[member.id]:
        doc = await load_user(member.id)
        old_level = doc["level"]
        if mode == "add":
            new_xp = doc["xp"] + value
        elif mode == "remove":
            new_xp = doc["xp"] - value
        else:
            new_xp = value
        doc["xp"] = max(0, new_xp)
        doc["level"] = level_from_xp(doc["xp"])[0]
        await users.replace_one({"_id": member.id}, doc, upsert=True)
    new_level = doc["level"]
    if new_level > old_level:
        await on_level_up(member, old_level, new_level, "admin")
    elif new_level < old_level:
        await sync_level_roles(member, new_level)
    return doc["xp"], new_level


# ============================================================
# المهام اليومية
# ============================================================

def daily_quests(uid):
    key = f"{uid}:{today_str()}"
    quests = quest_set_cache.get(key)
    if quests is None:
        quests = random.Random(key).sample(QUEST_POOL, 3)
        quest_set_cache[key] = quests
    return quests


async def get_quest_doc(uid):
    key = f"{uid}:{today_str()}"
    doc = quest_cache.get(key)
    if doc is None:
        doc = await quests_col.find_one({"_id": key})
        if doc is None:
            doc = {"_id": key, "p": {}, "done": [], "sets": {}}
        quest_cache[key] = doc
    return doc


async def quest_event(member, qid, inc=1, unique=None):
    quest = next((q for q in daily_quests(member.id) if q["id"] == qid), None)
    if quest is None:
        return
    finished = False
    async with user_locks[("q", member.id)]:
        doc = await get_quest_doc(member.id)
        if qid in doc["done"]:
            return
        if unique is not None:
            seen = doc["sets"].setdefault(qid, [])
            if unique in seen:
                return
            seen.append(unique)
            doc["p"][qid] = len(seen)
        else:
            doc["p"][qid] = doc["p"].get(qid, 0) + inc
        if doc["p"][qid] >= quest["target"]:
            doc["done"].append(qid)
            finished = True
        await quests_col.replace_one({"_id": doc["_id"]}, doc, upsert=True)
    if finished:
        await award_xp(member, quest["reward"], "other", use_mult=False)
        if QUEST_ANNOUNCE:
            text = quest["text"].format(t=quest["target"])
            embed = discord.Embed(
                title="مهمة منجزة",
                description=f"{member.mention}\n{text}",
                color=BEIGE,
            )
            embed.add_field(name="المكافأة", value=f"{quest['reward']} اكسبي", inline=True)
            embed.set_thumbnail(url=member.display_avatar.url)
            await send_announce(embed=embed, allowed=discord.AllowedMentions.none())


# ============================================================
# الروابط بين الاعضاء
# ============================================================

def bond_key(a, b):
    return f"{min(a, b)}:{max(a, b)}"


def bond_level(points):
    return int(math.sqrt(points / BOND_DIVISOR))


def add_bond(a, b, points):
    key = bond_key(a, b)
    old = bond_points.get(key, 0)
    new = old + points
    bond_points[key] = new
    bond_dirty.add(key)
    return bond_level(old), bond_level(new)


async def flush_bonds():
    if not bond_dirty:
        return
    keys = list(bond_dirty)
    bond_dirty.clear()
    ops = [UpdateOne({"_id": k}, {"$set": {"points": bond_points[k]}}, upsert=True) for k in keys]
    try:
        await bonds_col.bulk_write(ops, ordered=False)
    except Exception as e:
        bond_dirty.update(keys)
        print(f"bond flush error {e}")


async def handle_bond_up(guild, a_id, b_id, level, announce=True):
    reward = 60 + 40 * level
    first = None
    for uid in (a_id, b_id):
        member = guild.get_member(uid)
        if member:
            if first is None:
                first = member
            await award_xp(member, reward, "other", use_mult=False)
    if announce:
        embed = discord.Embed(
            title="ارتقاء رابط",
            description=f"<@{a_id}> و <@{b_id}>",
            color=BEIGE,
        )
        embed.add_field(name="المستوى الجديد", value=str(level), inline=True)
        embed.add_field(name="مكافأة كل واحد", value=f"{reward} اكسبي", inline=True)
        if first is not None:
            embed.set_thumbnail(url=first.display_avatar.url)
        await send_announce(embed=embed, allowed=discord.AllowedMentions.none())


# ============================================================
# الاكسبي من الصوت
# ============================================================

async def voice_tick():
    guild = get_guild()
    if guild is None:
        return
    afk_id = guild.afk_channel.id if guild.afk_channel else 0
    bond_announced = 0
    for channel in guild.voice_channels:
        if channel.id == afk_id or is_ignored_channel(channel.id):
            continue
        people = [m for m in channel.members if not m.bot and not has_ignored_role(m)]
        if not people:
            continue
        n = len(people)
        crowd = min(1.0 + CROWD_STEP * max(0, n - 2), CROWD_MAX)
        for m in people:
            base = VOICE_XP_PER_MIN * crowd
            if m.voice and (m.voice.self_video or m.voice.self_stream):
                base *= VOICE_CAM_BONUS
            await award_xp(m, int(round(base)), "voice", add_voice=1)
            await quest_event(m, "voice")
        if n <= BOND_MAX_ROOM:
            for a, b in combinations(people, 2):
                old, new = add_bond(a.id, b.id, BOND_VOICE_POINTS)
                await quest_event(a, "partners", unique=b.id)
                await quest_event(b, "partners", unique=a.id)
                if new > old:
                    can_announce = bond_announced < BOND_ANNOUNCE_LIMIT
                    if can_announce:
                        bond_announced += 1
                    await handle_bond_up(guild, a.id, b.id, new, announce=can_announce)


# ============================================================
# الاكسبي من الشات
# ============================================================

async def find_reply_target(message):
    author = None
    is_reply = False
    ref = message.reference
    if ref is not None and ref.message_id:
        resolved = ref.resolved
        if resolved is None:
            try:
                resolved = await message.channel.fetch_message(ref.message_id)
            except Exception:
                resolved = None
        if isinstance(resolved, discord.Message):
            author = resolved.author
            is_reply = True
    if author is None:
        for m in message.mentions:
            if not m.bot:
                author = m
                break
    if author is None or author.bot or author.id == message.author.id:
        return None, False
    member = message.guild.get_member(author.id)
    if member is None:
        return None, False
    return member, is_reply


async def handle_interaction(message, sender, target, is_reply):
    key = bond_key(sender.id, target.id)
    now = time.time()
    if now - pair_cd.get(key, 0) < 60:
        return
    pair_cd[key] = now
    await award_xp(sender, CONVO_XP_SENDER, "chat")
    await award_xp(target, CONVO_XP_TARGET, "chat")
    old, new = add_bond(sender.id, target.id, BOND_CHAT_POINTS)
    await quest_event(sender, "people", unique=target.id)
    await quest_event(target, "people", unique=sender.id)
    if is_reply:
        await quest_event(target, "replies")
    if new > old:
        await handle_bond_up(message.guild, sender.id, target.id, new)


async def handle_chat_xp(message):
    member = message.author
    if not isinstance(member, discord.Member):
        return
    channel = message.channel
    if is_ignored_channel(channel.id):
        return
    if has_ignored_role(member):
        return
    text = message.content.strip()
    now = time.time()
    if len(text) < 3:
        return
    last = last_msg.get(member.id)
    last_msg[member.id] = (text, now)
    if last and last[0] == text and now - last[1] < 120:
        return
    if now - last_xp.get(member.id, 0) < CHAT_COOLDOWN:
        return
    last_xp[member.id] = now
    amount = random.randint(CHAT_XP_MIN, CHAT_XP_MAX)
    await award_xp(member, amount, "chat", add_msgs=1)
    await quest_event(member, "chat")
    target, is_reply = await find_reply_target(message)
    if target is not None:
        await handle_interaction(message, member, target, is_reply)


# ============================================================
# بطاقات العرض
# ============================================================

async def build_rank_embed(guild, member):
    doc = await users.find_one({"_id": member.id}) or {}
    xp = doc.get("xp", 0)
    level, current, need = level_from_xp(xp)
    rank = await users.count_documents({"xp": {"$gt": xp}}) + 1
    embed = discord.Embed(color=BEIGE)
    embed.set_author(name=member.display_name, icon_url=member.display_avatar.url)
    if guild.icon:
        embed.set_thumbnail(url=guild.icon.url)
    embed.description = f"الحساب: {member.mention}\nاليوزر: @{member.name}"
    embed.add_field(name="المستوى", value=str(level), inline=True)
    embed.add_field(name="الاكسبي", value=str(xp), inline=True)
    embed.add_field(name="الترتيب", value=f"#{rank}", inline=True)
    embed.add_field(
        name="التقدم للمستوى القادم",
        value=f"{make_bar(current, need)} {current} / {need}",
        inline=False,
    )
    prestige = doc.get("prestige", 0)
    if prestige:
        embed.add_field(name="البريستيج", value=str(prestige), inline=True)
    embed.add_field(name="الرسائل", value=str(doc.get("msgs", 0)), inline=True)
    embed.add_field(name="دقائق الصوت", value=str(doc.get("voice_min", 0)), inline=True)
    if guild.icon:
        embed.set_footer(text=guild.name, icon_url=guild.icon.url)
    else:
        embed.set_footer(text=guild.name)
    return embed


async def fetch_avatar(member, size=128):
    if member is None:
        return None
    try:
        return await member.display_avatar.replace(size=size, format="png").read()
    except Exception:
        return None


def load_font(size):
    paths = [
        "/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf",
        "/usr/share/fonts/dejavu/DejaVuSans-Bold.ttf",
    ]
    for path in paths:
        try:
            return ImageFont.truetype(path, size)
        except Exception:
            continue
    return ImageFont.load_default(size)


def latin_only(text, fallback="User"):
    cleaned = "".join(c for c in text if 32 <= ord(c) < 127).strip()
    return cleaned or fallback


def fit_text(draw, text, font, max_width):
    while draw.textlength(text, font=font) > max_width and len(text) > 1:
        text = text[:-1]
    return text


# ------------------------------------------------------------
# بطاقة الترقية
# ------------------------------------------------------------

def card_background(width, height):
    if os.path.exists(BACKGROUND_PATH):
        try:
            bg = Image.open(BACKGROUND_PATH).convert("RGB")
            bg = ImageOps.fit(bg, (width, height))
            bg = bg.filter(ImageFilter.GaussianBlur(8))
            return Image.blend(bg, Image.new("RGB", (width, height), CARD_DEEP), 0.78)
        except Exception:
            pass
    bg = Image.new("RGB", (width, height), CARD_DEEP)
    gd = ImageDraw.Draw(bg)
    for y in range(height):
        t = y / height
        gd.line([(0, y), (width, y)], fill=(int(46 - 24 * t), int(34 - 18 * t), int(22 - 12 * t)))
    return bg


def card_glow(base, cx, cy, radius, blur, alpha):
    layer = Image.new("RGBA", base.size, (0, 0, 0, 0))
    ImageDraw.Draw(layer).ellipse(
        (cx - radius, cy - radius, cx + radius, cy + radius),
        fill=CARD_ACCENT + (alpha,),
    )
    layer = layer.filter(ImageFilter.GaussianBlur(blur))
    return Image.alpha_composite(base, layer)


def card_circle(image, diameter):
    image = ImageOps.fit(image, (diameter, diameter))
    scale = 4
    mask = Image.new("L", (diameter * scale, diameter * scale), 0)
    ImageDraw.Draw(mask).ellipse((0, 0, diameter * scale - 1, diameter * scale - 1), fill=255)
    mask = mask.resize((diameter, diameter), Image.LANCZOS)
    output = Image.new("RGBA", (diameter, diameter), (0, 0, 0, 0))
    output.paste(image, (0, 0), mask)
    return output


def card_digit_size(value, base):
    digits = len(str(value))
    if digits <= 2:
        return base
    if digits == 3:
        return int(base * 0.8)
    return int(base * 0.62)


def build_levelup_card(avatar_bytes, username, old_level, new_level, reason, guild_name):
    width, height = CARD_WIDTH, CARD_HEIGHT
    base = card_background(width, height).convert("RGBA")

    avatar_x, avatar_y, avatar_r = 150, 190, 110
    old_x, new_x, level_y = 410, 700, 205
    left, right = 310, 960
    middle = (left + right) // 2

    base = card_glow(base, avatar_x, avatar_y, 140, 40, 120)
    base = card_glow(base, new_x, level_y, 62, 22, 140)
    d = ImageDraw.Draw(base)

    avatar = None
    if avatar_bytes:
        try:
            avatar = Image.open(io.BytesIO(avatar_bytes)).convert("RGBA")
        except Exception:
            avatar = None
    if avatar is None:
        avatar = Image.new("RGBA", (256, 256), (90, 75, 55, 255))
    avatar = card_circle(avatar, avatar_r * 2)

    ring = 8
    d.ellipse(
        (avatar_x - avatar_r - ring, avatar_y - avatar_r - ring, avatar_x + avatar_r + ring, avatar_y + avatar_r + ring),
        fill=CARD_ACCENT,
    )
    base.paste(avatar, (avatar_x - avatar_r, avatar_y - avatar_r), avatar)
    d = ImageDraw.Draw(base)

    d.text((left, 30), "LEVEL UP", font=load_font(34), fill=CARD_ACCENT, anchor="la")
    d.text((right, 36), latin_only(guild_name, "Rav"), font=load_font(24), fill=CARD_MUTED, anchor="ra")

    f_name = load_font(50)
    name = fit_text(d, "@" + latin_only(username), f_name, right - left)
    d.text((left, 76), name, font=f_name, fill=(255, 255, 255), anchor="la")

    d.line([(left, 150), (right, 150)], fill=(90, 74, 54), width=2)

    d.ellipse(
        (old_x - 42, level_y - 42, old_x + 42, level_y + 42),
        fill=(34, 26, 18),
        outline=(120, 100, 75),
        width=4,
    )
    d.text(
        (old_x, level_y),
        str(old_level),
        font=load_font(card_digit_size(old_level, 40)),
        fill=CARD_MUTED,
        anchor="mm",
    )

    d.line([(old_x + 70, level_y), (new_x - 100, level_y)], fill=CARD_ACCENT, width=6)
    d.polygon(
        [(new_x - 72, level_y), (new_x - 98, level_y - 17), (new_x - 98, level_y + 17)],
        fill=CARD_ACCENT,
    )

    d.ellipse(
        (new_x - 52, level_y - 52, new_x + 52, level_y + 52),
        fill=CARD_ACCENT,
        outline=CARD_SOFT,
        width=4,
    )
    d.text(
        (new_x, level_y),
        str(new_level),
        font=load_font(card_digit_size(new_level, 54)),
        fill=CARD_DEEP,
        anchor="mm",
    )

    f_label = load_font(22)
    d.text((old_x, 266), "PREVIOUS LEVEL", font=f_label, fill=CARD_MUTED, anchor="ma")
    d.text((new_x, 266), "CURRENT LEVEL", font=f_label, fill=CARD_ACCENT, anchor="ma")

    d.rounded_rectangle(
        (left, 316, right, 364),
        radius=24,
        fill=(36, 28, 20),
        outline=(110, 90, 65),
        width=2,
    )
    f_reason = load_font(26)
    reason_text = fit_text(d, f"Reason: {reason}", f_reason, right - left - 40)
    d.text((middle, 340), reason_text, font=f_reason, fill=(255, 255, 255), anchor="mm")

    d.rounded_rectangle((1, 1, width - 2, height - 2), radius=36, outline=(150, 125, 90), width=3)
    mask = Image.new("L", (width, height), 0)
    ImageDraw.Draw(mask).rounded_rectangle((0, 0, width - 1, height - 1), radius=36, fill=255)
    base.putalpha(mask)

    buffer = io.BytesIO()
    base.save(buffer, format="PNG")
    buffer.seek(0)
    return buffer


async def send_levelup_card(member, old, new, reason):
    channel = await get_announce_channel()
    if channel is None:
        return
    try:
        avatar_bytes = await fetch_avatar(member, 256)
        reason_text = LEVEL_REASONS.get(reason, LEVEL_REASONS["other"])
        buffer = await asyncio.to_thread(
            build_levelup_card,
            avatar_bytes,
            member.name,
            old,
            new,
            reason_text,
            member.guild.name,
        )
        file = discord.File(buffer, filename="levelup.png")
        embed = discord.Embed(color=BEIGE)
        embed.set_image(url="attachment://levelup.png")
        await channel.send(
            content=member.mention,
            embed=embed,
            file=file,
            allowed_mentions=discord.AllowedMentions(users=True),
        )
    except Exception as e:
        print(f"levelup card error {e}")
        await send_announce(
            content=f"{member.mention} بسبب تواجدك في السيرفر تمت ترقيتك إلى مستوى {new} بعد ما كنت في مستوى {old}"
        )


# ------------------------------------------------------------
# لوحة المتصدرين
# ------------------------------------------------------------

def build_leaderboard_image(rows, guild_name):
    width, height = 1280, 860
    if os.path.exists(BACKGROUND_PATH):
        bg = Image.open(BACKGROUND_PATH).convert("RGB")
        scale = max(width / bg.width, height / bg.height)
        bg = bg.resize((int(bg.width * scale) + 1, int(bg.height * scale) + 1), Image.LANCZOS)
        left = (bg.width - width) // 2
        top = (bg.height - height) // 2
        bg = bg.crop((left, top, left + width, top + height))
    else:
        bg = Image.new("RGB", (width, height), (232, 217, 192))
        gd = ImageDraw.Draw(bg)
        for y in range(height):
            t = y / height
            color = (int(240 - 35 * t), int(228 - 44 * t), int(208 - 58 * t))
            gd.line([(0, y), (width, y)], fill=color)

    base = bg.convert("RGBA")
    overlay = Image.new("RGBA", (width, height), (0, 0, 0, 0))
    od = ImageDraw.Draw(overlay)
    od.rounded_rectangle((70, 130, width - 70, height - 30), radius=36, fill=(20, 14, 8, 130))
    row_h = 58
    gap = 6
    start_y = 150
    for i in range(len(rows)):
        y = start_y + i * (row_h + gap)
        od.rounded_rectangle((100, y, width - 100, y + row_h), radius=18, fill=(255, 255, 255, 38))
    base = Image.alpha_composite(base, overlay)

    d = ImageDraw.Draw(base)
    f_title = load_font(50)
    f_sub = load_font(24)
    f_name = load_font(28)
    f_small = load_font(24)

    d.text((width / 2, 62), "LEADERBOARD", font=f_title, fill=(255, 245, 225), anchor="mm")
    d.text((width / 2, 108), latin_only(guild_name, "Rav"), font=f_sub, fill=(232, 217, 192), anchor="mm")

    medal = {1: (255, 215, 0), 2: (215, 215, 215), 3: (205, 127, 50)}
    for i, row in enumerate(rows):
        rank = i + 1
        y = start_y + i * (row_h + gap)
        mid = y + row_h / 2
        color = medal.get(rank, (232, 217, 192))
        d.text((135, mid), str(rank), font=f_name, fill=color, anchor="mm")
        ax, ay, size = 175, int(y + (row_h - 46) / 2), 46
        if row["avatar"]:
            try:
                av = Image.open(io.BytesIO(row["avatar"])).convert("RGBA").resize((size, size), Image.LANCZOS)
                mask = Image.new("L", (size, size), 0)
                ImageDraw.Draw(mask).ellipse((0, 0, size - 1, size - 1), fill=255)
                base.paste(av, (ax, ay), mask)
            except Exception:
                d.ellipse((ax, ay, ax + size, ay + size), fill=(120, 105, 85, 255))
        else:
            d.ellipse((ax, ay, ax + size, ay + size), fill=(120, 105, 85, 255))
        name = fit_text(d, row["name"], f_name, 560)
        d.text((245, mid), name, font=f_name, fill=(255, 255, 255), anchor="lm")
        d.text((880, mid), f"Level {row['level']}", font=f_small, fill=(232, 217, 192), anchor="lm")
        d.text((width - 125, mid), f"{row['xp']} XP", font=f_small, fill=color, anchor="rm")

    buffer = io.BytesIO()
    base.convert("RGB").save(buffer, format="PNG")
    buffer.seek(0)
    return buffer


async def make_leaderboard(guild):
    top = await users.find({"xp": {"$gt": 0}}).sort("xp", -1).limit(10).to_list(10)
    if not top:
        return {"content": "ما فيه أحد في الترتيب للحين"}
    members = [guild.get_member(d["_id"]) for d in top]
    avatars = await asyncio.gather(*(fetch_avatar(m) for m in members))
    rows = []
    for doc, member, avatar in zip(top, members, avatars):
        rows.append({
            "name": latin_only(member.name) if member else "Left User",
            "level": doc.get("level", 0),
            "xp": doc["xp"],
            "avatar": avatar,
        })
    try:
        buffer = await asyncio.to_thread(build_leaderboard_image, rows, guild.name)
        return {"file": discord.File(buffer, filename="leaderboard.png")}
    except Exception as e:
        print(f"leaderboard image error {e}")
        lines = [f"#{i + 1} {r['name']} المستوى {r['level']} اكسبي {r['xp']}" for i, r in enumerate(rows)]
        embed = discord.Embed(title="لوحة المتصدرين", description="\n".join(lines), color=BEIGE)
        return {"embed": embed}


# ============================================================
# البوت والاحداث
# ============================================================

async def init_db():
    global mongo, users, bonds_col, quests_col, meta
    mongo = AsyncIOMotorClient(MONGO_URI)
    database = mongo["rav_pulse"]
    users = database["users"]
    bonds_col = database["bonds"]
    quests_col = database["quests"]
    meta = database["meta"]
    await users.create_index([("xp", -1)])


async def save_state():
    data = dict(STATE)
    await meta.replace_one({"_id": "state"}, {"_id": "state", **data}, upsert=True)


async def start_web():
    async def home(request):
        return web.Response(text="Rav Pulse is online")

    app = web.Application()
    app.add_routes([web.get("/", home)])
    runner = web.AppRunner(app)
    await runner.setup()
    site = web.TCPSite(runner, "0.0.0.0", int(os.getenv("PORT", "10000")))
    await site.start()


class PulseBot(commands.Bot):
    async def setup_hook(self):
        await init_db()
        saved = await meta.find_one({"_id": "state"})
        if saved:
            for key in STATE:
                if key in saved:
                    STATE[key] = saved[key]
        async for doc in bonds_col.find({}):
            bond_points[doc["_id"]] = doc.get("points", 0)
        LAST_DAY["value"] = today_str()
        await start_web()
        if GUILD_ID:
            guild_obj = discord.Object(id=GUILD_ID)
            self.tree.copy_global_to(guild=guild_obj)
            await self.tree.sync(guild=guild_obj)
        else:
            await self.tree.sync()
        tick.start()


intents = discord.Intents.default()
intents.members = True
intents.message_content = True
intents.voice_states = True

bot = PulseBot(command_prefix=commands.when_mentioned, intents=intents, help_command=None)


@bot.event
async def on_ready():
    await bot.change_presence(
        status=discord.Status.online,
        activity=discord.Streaming(name=STREAM_NAME, url=STREAM_URL),
    )
    print(f"Logged in as {bot.user}")


async def handle_xp_command(message):
    uid = message.author.id
    now = time.time()
    if now - xp_cmd_cd.get(uid, 0) < 4:
        return
    xp_cmd_cd[uid] = now
    target = None
    for m in message.mentions:
        if not m.bot:
            target = m
            break
    if target is None:
        target = message.author
    member = message.guild.get_member(target.id) or target
    embed = await build_rank_embed(message.guild, member)
    await message.reply(embed=embed, mention_author=False)


@bot.event
async def on_message(message):
    if message.author.bot or message.guild is None:
        return
    content = message.content.strip()
    first = content.split()[0] if content else ""
    if first == "اكسبي":
        await handle_xp_command(message)
        return
    if content in ("توب", "ليدربورد"):
        kwargs = await make_leaderboard(message.guild)
        await message.reply(**kwargs, mention_author=False)
        return
    await handle_chat_xp(message)


# ============================================================
# الحلقة الدورية كل دقيقة
# ============================================================

async def housekeeping():
    today = today_str()
    if LAST_DAY["value"] != today:
        LAST_DAY["value"] = today
        quest_cache.clear()
        quest_set_cache.clear()
    if len(pair_cd) > 5000:
        pair_cd.clear()
    if len(last_msg) > 5000:
        last_msg.clear()
    if len(last_xp) > 5000:
        last_xp.clear()
    now = time.time()
    if STATE["admin_mult_until"] and now >= STATE["admin_mult_until"]:
        STATE["admin_mult"] = 1.0
        STATE["admin_mult_until"] = 0.0
    await flush_bonds()
    await save_state()


@tasks.loop(seconds=60)
async def tick():
    for fn in (voice_tick, housekeeping):
        try:
            await fn()
        except Exception as e:
            print(f"tick error {fn.__name__} {e}")


@tick.before_loop
async def before_tick():
    await bot.wait_until_ready()


# ============================================================
# اوامر السلاش
# ============================================================

@bot.tree.command(name="rank", description="يعرض الاكسبي والمستوى")
@app_commands.describe(member="العضو")
async def rank_cmd(interaction: discord.Interaction, member: discord.Member = None):
    member = member or interaction.user
    embed = await build_rank_embed(interaction.guild, member)
    await interaction.response.send_message(embed=embed)


@bot.tree.command(name="leaderboard", description="لوحة المتصدرين في الاكسبي")
async def leaderboard_cmd(interaction: discord.Interaction):
    await interaction.response.defer()
    kwargs = await make_leaderboard(interaction.guild)
    await interaction.followup.send(**kwargs)


@bot.tree.command(name="pulse", description="نبض السيرفر والاحداث الحالية")
async def pulse_cmd(interaction: discord.Interaction):
    now = time.time()
    points = min(STATE["pulse"], PULSE_GOAL)
    embed = discord.Embed(title="نبض السيرفر", color=BEIGE)
    embed.add_field(
        name="العداد",
        value=f"{make_bar(points, PULSE_GOAL, 16)} {points} / {PULSE_GOAL}",
        inline=False,
    )
    if now < STATE["boost_until"]:
        left = int((STATE["boost_until"] - now) / 60) + 1
        embed.add_field(name="حدث النبض", value=f"اكسبي مضاعف ينتهي بعد {left} دقيقة", inline=False)
    if now < STATE["admin_mult_until"]:
        left = int((STATE["admin_mult_until"] - now) / 60) + 1
        embed.add_field(name="مضاعف الادارة", value=f"{STATE['admin_mult']} مرة لمدة {left} دقيقة", inline=False)
    await interaction.response.send_message(embed=embed)


@bot.tree.command(name="quests", description="مهامك اليومية")
async def quests_cmd(interaction: discord.Interaction):
    member = interaction.user
    doc = await get_quest_doc(member.id)
    lines = []
    for q in daily_quests(member.id):
        progress = min(doc["p"].get(q["id"], 0), q["target"])
        state = "تمت" if q["id"] in doc["done"] else f"{progress} / {q['target']}"
        lines.append(f"{q['text'].format(t=q['target'])}\nالتقدم {state} - المكافأة {q['reward']} اكسبي")
    embed = discord.Embed(title="مهامك اليومية", description="\n\n".join(lines), color=BEIGE)
    embed.set_footer(text="المهام تتجدد كل يوم عند منتصف الليل بتوقيت السعودية")
    await interaction.response.send_message(embed=embed, ephemeral=True)


@bot.tree.command(name="bonds", description="أقوى روابطك مع الأعضاء")
@app_commands.describe(member="العضو")
async def bonds_cmd(interaction: discord.Interaction, member: discord.Member = None):
    member = member or interaction.user
    mine = []
    for key, points in bond_points.items():
        a, b = key.split(":")
        a = int(a)
        b = int(b)
        if member.id in (a, b):
            other = b if a == member.id else a
            mine.append((points, other))
    mine.sort(reverse=True)
    top = mine[:5]
    if top:
        lines = [f"#{i + 1} <@{other}> المستوى {bond_level(points)} النقاط {points}" for i, (points, other) in enumerate(top)]
        text = "\n".join(lines)
    else:
        text = "ما عنده روابط للحين"
    embed = discord.Embed(title=f"روابط {member.display_name}", description=text, color=BEIGE)
    await interaction.response.send_message(embed=embed)


@bot.tree.command(name="prestige", description="ابدأ من جديد بعد الوصول لأعلى مستوى واحصل على بريستيج")
async def prestige_cmd(interaction: discord.Interaction):
    member = interaction.user
    async with user_locks[member.id]:
        doc = await load_user(member.id)
        if doc["level"] < PRESTIGE_LEVEL:
            await interaction.response.send_message(
                f"تحتاج مستوى {PRESTIGE_LEVEL} عشان تسوي بريستيج ومستواك الآن {doc['level']}",
                ephemeral=True,
            )
            return
        doc["xp"] = 0
        doc["level"] = 0
        doc["prestige"] += 1
        await users.replace_one({"_id": member.id}, doc, upsert=True)
    await sync_level_roles(member, 0)
    await interaction.response.send_message(f"مبروك {member.mention} وصلت للبريستيج {doc['prestige']}")


@bot.tree.command(name="xp_add", description="إضافة اكسبي لعضو")
@app_commands.describe(member="العضو", amount="الكمية")
@app_commands.checks.has_permissions(administrator=True)
async def xp_add_cmd(interaction: discord.Interaction, member: discord.Member, amount: int):
    xp, level = await change_xp(member, "add", amount)
    await interaction.response.send_message(f"تم التحديث اكسبي {member.mention} الآن {xp} والمستوى {level}", ephemeral=True)


@bot.tree.command(name="xp_remove", description="سحب اكسبي من عضو")
@app_commands.describe(member="العضو", amount="الكمية")
@app_commands.checks.has_permissions(administrator=True)
async def xp_remove_cmd(interaction: discord.Interaction, member: discord.Member, amount: int):
    xp, level = await change_xp(member, "remove", amount)
    await interaction.response.send_message(f"تم التحديث اكسبي {member.mention} الآن {xp} والمستوى {level}", ephemeral=True)


@bot.tree.command(name="xp_set", description="تحديد اكسبي عضو بقيمة معينة")
@app_commands.describe(member="العضو", amount="القيمة")
@app_commands.checks.has_permissions(administrator=True)
async def xp_set_cmd(interaction: discord.Interaction, member: discord.Member, amount: int):
    xp, level = await change_xp(member, "set", amount)
    await interaction.response.send_message(f"تم التحديث اكسبي {member.mention} الآن {xp} والمستوى {level}", ephemeral=True)


@bot.tree.command(name="xp_multiplier", description="تشغيل مضاعف اكسبي لكل السيرفر")
@app_commands.describe(value="قيمة المضاعف", minutes="المدة بالدقائق")
@app_commands.checks.has_permissions(administrator=True)
async def xp_multiplier_cmd(interaction: discord.Interaction, value: float, minutes: int):
    STATE["admin_mult"] = max(1.0, min(value, 10.0))
    STATE["admin_mult_until"] = time.time() + max(1, minutes) * 60
    await save_state()
    embed = discord.Embed(
        title="حدث اكسبي مضاعف",
        description=f"صار الاكسبي مضاعف {STATE['admin_mult']} مرة لمدة {minutes} دقيقة",
        color=BEIGE,
    )
    await send_announce(embed=embed)
    await interaction.response.send_message("تم تشغيل المضاعف", ephemeral=True)


@bot.tree.command(name="ignore_channel", description="تفعيل أو إلغاء منع الاكسبي في روم")
@app_commands.describe(channel="الروم")
@app_commands.checks.has_permissions(administrator=True)
async def ignore_channel_cmd(interaction: discord.Interaction, channel: discord.abc.GuildChannel):
    if channel.id in STATE["ignored"]:
        STATE["ignored"].remove(channel.id)
        text = f"رجع الاكسبي يشتغل في {channel.mention}"
    else:
        STATE["ignored"].append(channel.id)
        text = f"تم منع الاكسبي في {channel.mention}"
    await save_state()
    await interaction.response.send_message(text, ephemeral=True)


@bot.tree.error
async def on_tree_error(interaction: discord.Interaction, error: app_commands.AppCommandError):
    if isinstance(error, app_commands.MissingPermissions):
        message = "هذا الأمر للإدارة فقط"
    else:
        message = "صار خطأ بسيط حاول مرة ثانية"
        print(f"command error {error}")
    if interaction.response.is_done():
        await interaction.followup.send(message, ephemeral=True)
    else:
        await interaction.response.send_message(message, ephemeral=True)


bot.run(TOKEN)
