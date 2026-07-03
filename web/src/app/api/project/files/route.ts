import fs from 'node:fs'
import path from 'node:path'
import { resolveFs } from '@/lib/server/paths'

export const dynamic = 'force-dynamic'
export const runtime = 'nodejs'

const EXCLUDED = new Set([
  '.lake', '.git', 'node_modules', '__pycache__', '.venv',
  'target', '.next', 'out', 'build', 'dist', '.reference',
])

interface Node { name: string; type: 'file' | 'directory'; path: string; size?: number; children?: Node[] }

function scan(dir: string): Node[] {
  let items: fs.Dirent[]
  try { items = fs.readdirSync(dir, { withFileTypes: true }) } catch { return [] }
  // Directories before files, then by name.
  const sorted = items.sort((a, b) => {
    const af = a.isFile() ? 1 : 0, bf = b.isFile() ? 1 : 0
    return af - bf || a.name.localeCompare(b.name)
  })
  const out: Node[] = []
  for (const it of sorted) {
    if (it.name.startsWith('.') && it.name !== '.astrolabe') continue
    if (EXCLUDED.has(it.name)) continue
    const fp = path.join(dir, it.name)
    if (it.isDirectory()) out.push({ name: it.name, type: 'directory', path: fp, children: scan(fp) })
    else {
      let size = 0
      try { size = fs.statSync(fp).size } catch { /* ignore */ }
      out.push({ name: it.name, type: 'file', path: fp, size })
    }
  }
  return out
}

export async function GET(req: Request) {
  const { searchParams } = new URL(req.url)
  const raw = searchParams.get('path')
  if (!raw) return Response.json({ detail: 'path required' }, { status: 400 })
  const projectPath = resolveFs(raw)
  if (!fs.existsSync(projectPath)) return Response.json([])
  return Response.json(scan(projectPath))
}
