/**
 * Plugin interface decoupling tests.
 *
 * Core files must not import from or reference any specific plugin.
 */
import { describe, it, expect } from 'vitest'
import * as fs from 'fs'

const entryDetail = fs.readFileSync('src/panels/workspace/EntryDetail.tsx', 'utf-8')
const networkView = fs.readFileSync('src/panels/workspace/NetworkView.tsx', 'utf-8')
const networkSettings = fs.readFileSync('src/panels/workspace/NetworkSettings.tsx', 'utf-8')
const pluginTypes = fs.readFileSync('src/plugins/types.ts', 'utf-8')

describe('Core files have no direct plugin imports', () => {
    it('EntryDetail does not import from leannets', () => {
        expect(entryDetail).not.toMatch(/from\s+['"].*\/plugins\/leannets/)
    })

    it('NetworkView does not import from leannets', () => {
        expect(networkView).not.toMatch(/from\s+['"].*\/plugins\/leannets/)
    })

    it('NetworkSettings does not import from leannets', () => {
        expect(networkSettings).not.toMatch(/from\s+['"].*\/plugins\/leannets/)
    })
})

describe('Core files have no hardcoded plugin id', () => {
    it('EntryDetail has no leannets string', () => {
        expect(entryDetail).not.toContain("'leannets'")
        expect(entryDetail).not.toContain('"leannets"')
    })

    it('NetworkView has no leannets string', () => {
        expect(networkView).not.toContain("'leannets'")
        expect(networkView).not.toContain('"leannets"')
    })

    it('NetworkSettings has no leannets string', () => {
        expect(networkSettings).not.toContain("'leannets'")
        expect(networkSettings).not.toContain('"leannets"')
    })
})

describe('Plugin interface has required fields', () => {
    it('has RecordRenderer', () => {
        expect(pluginTypes).toContain('RecordRenderer')
    })

    it('has networkMode', () => {
        expect(pluginTypes).toContain('networkMode')
    })

    it('has SettingsPanel', () => {
        expect(pluginTypes).toContain('SettingsPanel')
    })
})
