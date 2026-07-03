import fs from 'node:fs'
import path from 'node:path'
import { resolveFs } from '@/lib/server/paths'

export const dynamic = 'force-dynamic'
export const runtime = 'nodejs'

export async function GET(req: Request) {
  const { searchParams } = new URL(req.url)
  const projectPath = searchParams.get('path')
  const file = searchParams.get('file')
  if (!projectPath || !file) return Response.json({ detail: 'path and file required' }, { status: 400 })

  // Containment: only files inside the project's .astrolabe/docs are readable.
  const root = path.resolve(resolveFs(projectPath), '.astrolabe', 'docs')
  const filePath = path.resolve(root, file)
  if (!filePath.startsWith(root + path.sep)) return Response.json({ detail: 'Access denied' }, { status: 403 })
  if (!fs.existsSync(filePath) || !fs.statSync(filePath).isFile())
    return Response.json({ detail: 'File not found' }, { status: 404 })
  return Response.json({ content: fs.readFileSync(filePath, 'utf8'), name: path.basename(filePath) })
}
